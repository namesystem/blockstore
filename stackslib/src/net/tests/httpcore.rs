// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020-2023 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
use std::sync::mpsc::{channel, Receiver};
use std::time::{Duration, Instant};
use std::{str, thread};

use stacks_common::codec::StacksMessageCodec;
use stacks_common::types::chainstate::{StacksAddress, StacksBlockId, StacksPrivateKey};
use stacks_common::types::net::{PeerAddress, PeerHost};
use stacks_common::types::StacksEpochId;
use stacks_common::util::chunked_encoding::{
    HttpChunkedTransferWriter, HttpChunkedTransferWriterState,
};
use stacks_common::util::hash::{hex_bytes, to_hex, Hash160};

use crate::burnchains::Txid;
use crate::chainstate::stacks::db::blocks::test::make_sample_microblock_stream;
use crate::chainstate::stacks::test::make_codec_test_block;
use crate::chainstate::stacks::{
    StacksTransaction, TokenTransferMemo, TransactionAuth, TransactionPayload,
    TransactionPostConditionMode, TransactionVersion,
};
use crate::net::api::getneighbors::{RPCNeighbor, RPCNeighborsInfo};
use crate::net::connection::ConnectionOptions;
use crate::net::http::{
    http_error_from_code_and_text, http_reason, HttpContentType, HttpErrorResponse,
    HttpRequestContents, HttpRequestPreamble, HttpReservedHeader, HttpResponsePayload,
    HttpResponsePreamble, HttpVersion, HTTP_PREAMBLE_MAX_NUM_HEADERS,
};
use crate::net::httpcore::{
    send_http_request, CostTracker, HttpPreambleExtensions, HttpRequestContentsExtensions,
    StacksHttp, StacksHttpMessage, StacksHttpPreamble, StacksHttpRequest, StacksHttpResponse,
};
use crate::net::rpc::ConversationHttp;
use crate::net::{ProtocolFamily, TipRequest};

#[test]
fn test_parse_stacks_http_preamble_request_err() {
    let tests = vec![
        (
            "GET /foo HTTP/1.1\r\n",
            "Not enough bytes to form a HTTP request or response",
        ),
        (
            "GET /foo HTTP/1.1\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
        (
            "GET /foo HTTP/1.1\r\nFoo: Bar\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
        (
            "GET /foo HTTP/\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
        (
            "GET /foo HTTP/1.1\r\nHost:",
            "Not enough bytes to form a HTTP request or response",
        ),
        (
            "GET /foo HTTP/1.1\r\nHost: foo:80\r\nHost: bar:80\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
        (
            "GET /foo HTTP/1.1\r\nHost: localhost:6270\r\nfoo: \u{2764}\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
        (
            "Get /foo HTTP/1.1\r\nHost: localhost:666666\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
        (
            "GET /foo HTTP/1.1\r\nHost: localhost:8080\r\nConnection: foo\r\n\r\n",
            "Failed to decode HTTP request or HTTP response",
        ),
    ];

    for (data, errstr) in tests.iter() {
        let sres = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
        test_debug!("Expect '{}'", errstr);
        assert!(sres.is_err(), "{:?}", &sres);
        assert!(
            sres.as_ref()
                .unwrap_err()
                .to_string()
                .find(errstr)
                .is_some(),
            "{:?}",
            &sres
        );
    }
}

#[test]
fn test_parse_stacks_http_preamble_response_err() {
    let tests = vec![
        ("HTTP/1.1 200",
        "Not enough bytes to form a HTTP request or response"),
        ("HTTP/1.1 200 OK\r\nfoo: \u{2764}\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
        ("HTTP/1.1 200 OK\r\nfoo: bar\r\nfoo: bar\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
        ("HTTP/1.1 200 OK\r\nContent-Type: image/png\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
        ("HTTP/1.1 200 OK\r\nContent-Length: foo\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
        ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
        ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 123\r\nTransfer-Encoding: chunked\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
        ("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 123\r\nConnection: foo\r\n\r\n",
         "Failed to decode HTTP request or HTTP response"),
    ];

    for (data, errstr) in tests.iter() {
        let sres = StacksHttpPreamble::consensus_deserialize(&mut data.as_bytes());
        test_debug!("Expect '{}', got: {:?}", errstr, &sres);
        assert!(sres.is_err(), "{:?}", &sres);
        assert!(
            sres.as_ref()
                .unwrap_err()
                .to_string()
                .find(errstr)
                .is_some(),
            "{:?}",
            &sres
        );
    }
}

fn make_test_transaction() -> StacksTransaction {
    let privk = StacksPrivateKey::from_hex(
        "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
    )
    .unwrap();
    let auth = TransactionAuth::from_p2pkh(&privk).unwrap();
    let addr = auth.origin().address_testnet();
    let recv_addr = StacksAddress::new(1, Hash160([0xff; 20])).unwrap();

    let mut tx_stx_transfer = StacksTransaction::new(
        TransactionVersion::Testnet,
        auth,
        TransactionPayload::TokenTransfer(
            recv_addr.clone().into(),
            123,
            TokenTransferMemo([0u8; 34]),
        ),
    );
    tx_stx_transfer.chain_id = 0x80000000;
    tx_stx_transfer.post_condition_mode = TransactionPostConditionMode::Allow;
    tx_stx_transfer.set_tx_fee(0);
    tx_stx_transfer
}

#[test]
fn test_http_request_type_codec() {
    let convo = ConversationHttp::new(
        "127.0.0.1:12345".parse().unwrap(),
        None,
        PeerHost::DNS("localhost".to_string(), 12345),
        &ConnectionOptions::default(),
        100,
        32,
    );
    let tx = make_test_transaction();
    let tx_body = tx.serialize_to_vec();

    let fixtures = vec![
        (
            StacksHttpRequest::new_getneighbors(convo.get_peer_host()),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/neighbors".to_string(),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getinfo(convo.get_peer_host(), Some(1234)),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/info".to_string(),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getinfo(convo.get_peer_host(), None),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/info".to_string(),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getpoxinfo(convo.get_peer_host(), TipRequest::UseLatestUnconfirmedTip),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/pox?tip=latest".to_string(),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getpoxinfo(convo.get_peer_host(), TipRequest::UseLatestAnchoredTip),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/pox".to_string(),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getheaders(convo.get_peer_host(), 2100, TipRequest::SpecificTip(StacksBlockId([0x80; 32]))),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                "/v2/headers/2100?tip=8080808080808080808080808080808080808080808080808080808080808080".to_string(),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getblock(convo.get_peer_host(), StacksBlockId([2u8; 32])),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                format!("/v2/blocks/{}", StacksBlockId([2u8; 32]).to_hex()),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_getmicroblocks_indexed(convo.get_peer_host(), StacksBlockId([3u8; 32])),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "GET".to_string(),
                format!("/v2/microblocks/{}", StacksBlockId([3u8; 32]).to_hex()),
                "localhost".to_string(),
                12345,
                true,
            ),
            vec![]
        ),
        (
            StacksHttpRequest::new_post_transaction(convo.get_peer_host(), tx.clone()),
            HttpRequestPreamble::new(
                HttpVersion::Http11,
                "POST".to_string(),
                "/v2/transactions".to_string(),
                "localhost".to_string(),
                12345,
                true,
            )
            .with_content_type(HttpContentType::Bytes)
            .with_content_length(tx.serialize_to_vec().len() as u32),
            tx_body
        )
    ];

    for (mut test, mut expected_http_preamble, expected_http_body) in fixtures.into_iter() {
        if test.preamble().get_request_id().is_none() {
            test.preamble_mut().set_request_id(123);
        }
        expected_http_preamble.set_request_id(test.preamble().get_request_id().unwrap_or(0));
        if let Some(h) = test.preamble().get_canonical_stacks_tip_height() {
            expected_http_preamble.set_canonical_stacks_tip_height(Some(h));
        }

        let mut expected_bytes = vec![];
        expected_http_preamble
            .consensus_serialize(&mut expected_bytes)
            .unwrap();

        test_debug!(
            "Expected preamble:\n{}",
            str::from_utf8(&expected_bytes).unwrap()
        );

        if !expected_http_body.is_empty() {
            expected_http_preamble.set_content_type(HttpContentType::Bytes);
            expected_http_preamble.set_content_length(expected_http_body.len() as u32)
        }

        if expected_http_preamble.content_type.is_none()
            || expected_http_preamble.content_type != Some(HttpContentType::Bytes)
        {
            test_debug!(
                "Expected http body:\n{}",
                str::from_utf8(&expected_http_body).unwrap()
            );
        } else {
            test_debug!("Expected http body (hex):\n{}", to_hex(&expected_http_body));
        }

        expected_bytes.append(&mut expected_http_body.clone());

        let mut bytes = vec![];
        let mut http = StacksHttp::new(
            "127.0.0.1:12345".parse().unwrap(),
            &ConnectionOptions::default(),
        );
        http.write_message(&mut bytes, &StacksHttpMessage::Request(test.clone()))
            .unwrap();

        assert_eq!(bytes, expected_bytes);
    }
}

#[test]
fn test_http_request_type_codec_err() {
    let bad_content_lengths = vec![
        "GET /v2/neighbors HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        "GET /v2/info HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        "GET /v2/pox HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        "GET /v2/headers/2100 HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        "GET /v2/blocks/1111111111111111111111111111111111111111111111111111111111111111 HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        "GET /v2/microblocks/1111111111111111111111111111111111111111111111111111111111111111 HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
        "POST /v2/transactions HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 0\r\n\r\n",
    ];
    for bad_content_length in bad_content_lengths {
        let mut http = StacksHttp::new(
            "127.0.0.1:20443".parse().unwrap(),
            &ConnectionOptions::default(),
        );
        let (preamble, offset) = http.read_preamble(bad_content_length.as_bytes()).unwrap();
        let e = http.read_payload(&preamble, &bad_content_length.as_bytes()[offset..]);

        if let Ok(http_error) = e {
            debug!("Got HTTP error: {:?}", &http_error);

            let error_str = format!("{:?}", &http_error);
            assert!(error_str.find("-length body").is_some());
            assert!(error_str.find("status_code: 400").is_some());
        } else {
            panic!("Expected error");
        }
    }

    let bad_content_types = vec![
        "POST /v2/transactions HTTP/1.1\r\nUser-Agent: stacks/2.0\r\nHost: bad:123\r\nContent-Length: 1\r\n\r\nb",
    ];
    for bad_content_type in bad_content_types {
        let mut http = StacksHttp::new(
            "127.0.0.1:20443".parse().unwrap(),
            &ConnectionOptions::default(),
        );
        let (preamble, offset) = http.read_preamble(bad_content_type.as_bytes()).unwrap();
        let e = http.read_payload(&preamble, &bad_content_type.as_bytes()[offset..]);

        if let Ok(http_error) = e {
            debug!("Got HTTP error: {:?}", &http_error);

            let error_str = format!("{:?}", &http_error);
            assert!(error_str.find("Missing Content-Type").is_some());
            assert!(error_str.find("status_code: 400").is_some());
        } else {
            panic!("Expected error");
        }
    }
}

#[test]
fn test_http_response_type_codec() {
    let test_neighbors_info = RPCNeighborsInfo {
        bootstrap: vec![],
        sample: vec![
            RPCNeighbor {
                network_id: 1,
                peer_version: 2,
                addrbytes: PeerAddress([
                    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
                    0x0d, 0x0e, 0x0f,
                ]),
                port: 12345,
                public_key_hash: Hash160::from_bytes(
                    &hex_bytes("1111111111111111111111111111111111111111").unwrap(),
                )
                .unwrap(),
                authenticated: true,
                stackerdbs: Some(vec![]),
                age: None,
            },
            RPCNeighbor {
                network_id: 3,
                peer_version: 4,
                addrbytes: PeerAddress([
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0x01,
                    0x02, 0x03, 0x04,
                ]),
                port: 23456,
                public_key_hash: Hash160::from_bytes(
                    &hex_bytes("2222222222222222222222222222222222222222").unwrap(),
                )
                .unwrap(),
                authenticated: false,
                stackerdbs: Some(vec![]),
                age: None,
            },
        ],
        inbound: vec![],
        outbound: vec![],
    };

    let privk = StacksPrivateKey::from_hex(
        "6d430bb91222408e7706c9001cfaeb91b08c2be6d5ac95779ab52c6b431950e001",
    )
    .unwrap();
    let test_block_info = make_codec_test_block(5, StacksEpochId::latest());
    let test_microblock_info = make_sample_microblock_stream(&privk, &test_block_info.block_hash());

    let mut test_block_info_bytes = vec![];
    test_block_info
        .consensus_serialize(&mut test_block_info_bytes)
        .unwrap();

    let mut test_microblock_info_bytes = vec![];
    test_microblock_info
        .consensus_serialize(&mut test_microblock_info_bytes)
        .unwrap();

    let tests = vec![
        // length is known
        (
            StacksHttpResponse::new_getneighbors(test_neighbors_info.clone(), true),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_getblock(test_block_info.clone(), true),
            "GET".to_string(),
            format!("/v2/blocks/{}", test_block_info.block_hash().to_hex()),
        ),
        (
            StacksHttpResponse::new_getmicroblocks_indexed(test_microblock_info.clone(), true),
            "GET".to_string(),
            format!(
                "/v2/microblocks/{}",
                test_microblock_info[0].block_hash().to_hex()
            ),
        ),
        (
            StacksHttpResponse::new_posttransaction(Txid([0x01; 32]), true),
            "POST".to_string(),
            "/v2/transactions".to_string(),
        ),
        // length is unknown
        (
            StacksHttpResponse::new_getneighbors(test_neighbors_info.clone(), false),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_getblock(test_block_info.clone(), false),
            "GET".to_string(),
            format!("/v2/blocks/{}", test_block_info.block_hash().to_hex()),
        ),
        (
            StacksHttpResponse::new_getmicroblocks_indexed(test_microblock_info.clone(), false),
            "GET".to_string(),
            format!(
                "/v2/microblocks/{}",
                test_microblock_info[0].block_hash().to_hex()
            ),
        ),
        (
            StacksHttpResponse::new_posttransaction(Txid([0x01; 32]), false),
            "POST".to_string(),
            "/v2/transactions".to_string(),
        ),
        // errors without error messages
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(400, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(401, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(402, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(403, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(404, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(500, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(503, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(502, "".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        // errors with specific messages
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(400, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(401, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(402, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(403, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(404, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(500, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(503, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
        (
            StacksHttpResponse::new_empty_error(&*http_error_from_code_and_text(502, "foo".into())),
            "GET".to_string(),
            "/v2/neighbors".to_string(),
        ),
    ];
    let expected_http_preambles = vec![
        // length is known
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            Some(serde_json::to_string(&test_neighbors_info).unwrap().len() as u32),
            HttpContentType::JSON,
            true,
        ),
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            Some(test_block_info.serialize_to_vec().len() as u32),
            HttpContentType::Bytes,
            true,
        ),
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            Some(test_microblock_info_bytes.len() as u32),
            HttpContentType::Bytes,
            true,
        ),
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            Some((Txid([0x01; 32]).to_hex().len() + 2) as u32),
            HttpContentType::JSON,
            true,
        ),
        // length is unknown
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            None,
            HttpContentType::JSON,
            true,
        ),
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            None,
            HttpContentType::Bytes,
            true,
        ),
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            None,
            HttpContentType::Bytes,
            true,
        ),
        HttpResponsePreamble::new(
            HttpVersion::Http11,
            200,
            "OK".to_string(),
            None,
            HttpContentType::JSON,
            true,
        ),
        // errors
        HttpResponsePreamble::error_text(400, http_reason(400), ""),
        HttpResponsePreamble::error_text(401, http_reason(401), ""),
        HttpResponsePreamble::error_text(402, http_reason(402), ""),
        HttpResponsePreamble::error_text(403, http_reason(403), ""),
        HttpResponsePreamble::error_text(404, http_reason(404), ""),
        HttpResponsePreamble::error_text(500, http_reason(500), ""),
        HttpResponsePreamble::error_text(503, http_reason(503), ""),
        // generic error
        HttpResponsePreamble::error_text(502, http_reason(502), ""),
        // errors with messages
        HttpResponsePreamble::error_text(400, http_reason(400), "foo"),
        HttpResponsePreamble::error_text(401, http_reason(401), "foo"),
        HttpResponsePreamble::error_text(402, http_reason(402), "foo"),
        HttpResponsePreamble::error_text(403, http_reason(403), "foo"),
        HttpResponsePreamble::error_text(404, http_reason(404), "foo"),
        HttpResponsePreamble::error_text(500, http_reason(500), "foo"),
        HttpResponsePreamble::error_text(503, http_reason(503), "foo"),
        // generic error
        HttpResponsePreamble::error_text(502, http_reason(502), "foo"),
    ];

    let expected_http_bodies = vec![
        // with content-length
        serde_json::to_string(&test_neighbors_info)
            .unwrap()
            .as_bytes()
            .to_vec(),
        test_block_info.serialize_to_vec(),
        test_microblock_info_bytes.clone(),
        Txid([0x1; 32]).to_hex().as_bytes().to_vec(),
        // with transfer-encoding: chunked
        serde_json::to_string(&test_neighbors_info)
            .unwrap()
            .as_bytes()
            .to_vec(),
        test_block_info.serialize_to_vec(),
        test_microblock_info_bytes.clone(),
        Txid([0x1; 32]).to_hex().as_bytes().to_vec(),
        // errors
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
        // errors with messages
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
        "foo".as_bytes().to_vec(),
    ];

    for ((test, request_verb, request_path), (expected_http_preamble, _expected_http_body)) in
        tests.iter().zip(
            expected_http_preambles
                .iter()
                .zip(expected_http_bodies.iter()),
        )
    {
        let mut http = StacksHttp::new(
            "127.0.0.1:20443".parse().unwrap(),
            &ConnectionOptions::default(),
        );
        let mut bytes = vec![];
        test_debug!("write body:\n{:?}\n", test);

        http.write_message(&mut bytes, &StacksHttpMessage::Response((*test).clone()))
            .unwrap();

        http.set_response_handler(request_verb, request_path);
        let (mut preamble, offset) = http
            .read_preamble(&bytes)
            .unwrap_or_else(|e| panic!("first 4096 bytes:\n{bytes:?}\nerror: {e:?}"));

        test_debug!(
            "{request_verb} {request_path}: read preamble of {offset} bytes\n{preamble:?}\n",
        );

        let (mut message, _total_len) = if expected_http_preamble.is_chunked() {
            let (msg_opt, len) = http
                .stream_payload(&preamble, &mut &bytes[offset..])
                .unwrap();
            (msg_opt.unwrap().0, len)
        } else {
            http.read_payload(&preamble, &bytes[offset..]).unwrap()
        };

        test_debug!("got message\n{:?}\n", &message);

        // check everything in the parsed preamble except for the extra headers
        if let StacksHttpPreamble::Response(req) = &mut preamble {
            assert_eq!(req.headers.len(), 5);
            assert!(req.headers.contains_key("access-control-allow-headers"));
            assert!(req.headers.contains_key("access-control-allow-methods"));
            assert!(req.headers.contains_key("access-control-allow-origin"));
            assert!(req.headers.contains_key("server"));
            assert!(req.headers.contains_key("date"));
            req.headers.clear();
        } else {
            panic!("Unexpected preamble");
        }

        assert_eq!(
            preamble,
            StacksHttpPreamble::Response((*expected_http_preamble).clone())
        );

        // note that message's headers contain cors headers and the like, which we don't synthesize
        // here
        if let StacksHttpMessage::Response(response) = &mut message {
            response.clear_headers();
        } else {
            panic!("Not an HTTP response");
        }
        assert_eq!(message, StacksHttpMessage::Response((*test).clone()));
        assert_eq!(http.num_pending(), 0);
    }
}

#[test]
fn test_http_response_type_codec_err() {
    let request_paths = vec![
        (
            "GET",
            "/v2/blocks/1111111111111111111111111111111111111111111111111111111111111111",
        ),
        ("POST", "/v2/transactions"),
        ("GET", "/v2/neighbors"),
        ("GET", "/v2/neighbors"),
        ("GET", "/v2/neighbors"),
    ];
    let bad_request_payloads = [
        "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 2\r\n\r\nab",
        "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 4\r\n\r\n\"ab\"",
        "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 1\r\n\r\n{",
        "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nContent-length: 1\r\n\r\na",
        "HTTP/1.1 400 Bad Request\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/octet-stream\r\nContent-length: 2\r\n\r\n{}",
    ];
    let expected_bad_request_payload_errors = [
        "Invalid content-type",
        "bad length 2 for hex string",
        "Not enough bytes",
        "Failed to parse",
        "expected text/plain",
    ];
    for (test, (expected_error, (request_verb, request_path))) in bad_request_payloads.iter().zip(
        expected_bad_request_payload_errors
            .iter()
            .zip(request_paths),
    ) {
        test_debug!(
            "Expect failure:\n{}\nExpected error: '{}'",
            test,
            expected_error
        );

        let mut http = StacksHttp::new(
            "127.0.0.1:20443".parse().unwrap(),
            &ConnectionOptions::default(),
        );
        http.set_response_handler(request_verb, request_path);

        let (preamble, offset) = http.read_preamble(test.as_bytes()).unwrap();
        let e = http.read_payload(&preamble, &test.as_bytes()[offset..]);
        let errstr = format!("{:?}", &e);
        assert!(e.is_err());
        assert!(
            e.unwrap_err().to_string().find(expected_error).is_some(),
            "{}",
            errstr
        );
    }
}

#[test]
fn test_http_duplicate_concurrent_streamed_response_fails() {
    // do not permit multiple in-flight chunk-encoded HTTP responses with the same request ID.
    let valid_neighbors_response = "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\n\r\n37\r\n{\"bootstrap\":[],\"sample\":[],\"inbound\":[],\"outbound\":[]}\r\n0\r\n\r\n";
    let invalid_neighbors_response = "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\n\r\n10\r\nxxxxxxxxxxxxxxxx\r\n0\r\n\r\n";
    let invalid_chunked_response = "HTTP/1.1 200 OK\r\nServer: stacks/v2.0\r\nX-Request-Id: 123\r\nContent-Type: application/json\r\nTransfer-Encoding: chunked\r\n\r\n38\r\n{\"bootstrap\":[],\"sample\":[],\"inbound\":[],\"outbound\":[]}\r\n0\r\n\r\n";

    let mut http = StacksHttp::new(
        "127.0.0.1:20443".parse().unwrap(),
        &ConnectionOptions::default(),
    );

    http.set_response_handler("GET", "/v2/neighbors");
    let (preamble, offset) = http
        .read_preamble(valid_neighbors_response.as_bytes())
        .unwrap();
    assert_eq!(http.num_pending(), 1);

    // can't do this twice
    http.set_response_handler("GET", "/v2/neighbors");
    let res = http.read_preamble(valid_neighbors_response.as_bytes());
    assert!(res.is_err());
    assert!(res.unwrap_err().to_string().find("in progress").is_some());

    // finish reading the body
    let msg = http
        .stream_payload(
            &preamble,
            &mut &valid_neighbors_response.as_bytes()[offset..],
        )
        .unwrap();
    if let (Some((StacksHttpMessage::Response(response), _)), _) = msg {
        assert_eq!(
            response.decode_rpc_neighbors().unwrap(),
            RPCNeighborsInfo {
                bootstrap: vec![],
                sample: vec![],
                inbound: vec![],
                outbound: vec![]
            }
        )
    } else {
        panic!("Got {msg:?}");
    }
    assert_eq!(http.num_pending(), 0);

    // can read the preamble again, but only once
    http.set_response_handler("GET", "/v2/neighbors");
    let (preamble, offset) = http
        .read_preamble(invalid_neighbors_response.as_bytes())
        .unwrap();
    assert_eq!(http.num_pending(), 1);

    http.set_response_handler("GET", "/v2/neighbors");
    let res = http.read_preamble(valid_neighbors_response.as_bytes());
    assert!(res.is_err());
    assert!(res.unwrap_err().to_string().find("in progress").is_some());

    // reading a corrupt body unlocks the ability to read the preamble again
    let res = http.stream_payload(
        &preamble,
        &mut &invalid_neighbors_response.as_bytes()[offset..],
    );
    assert!(res.unwrap_err().to_string().find("JSON").is_some());
    assert_eq!(http.num_pending(), 0);

    // can read the premable again, but only once
    http.set_response_handler("GET", "/v2/neighbors");
    let (preamble, offset) = http
        .read_preamble(invalid_chunked_response.as_bytes())
        .unwrap();

    http.set_response_handler("GET", "/v2/neighbors");
    let res = http.read_preamble(valid_neighbors_response.as_bytes());

    assert!(res.is_err());
    assert!(res.unwrap_err().to_string().find("in progress").is_some());

    // reading a corrupt chunk stream unlocks the ability to read the preamble again
    let res = http.stream_payload(
        &preamble,
        &mut &invalid_chunked_response.as_bytes()[offset..],
    );
    assert!(res
        .unwrap_err()
        .to_string()
        .find("Invalid chunk trailer")
        .is_some());
    assert_eq!(http.num_pending(), 0);
}

#[test]
fn test_http_parse_proof_tip_query() {
    let query_txt = "tip=7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392";
    let tip_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .tip_request();
    let block_id =
        StacksBlockId::from_hex("7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392")
            .unwrap();
    assert!(matches!(tip_req, TipRequest::SpecificTip(block_id)));

    // last parseable tip is taken
    let query_txt_dup = "tip=7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392&tip=03e26bd68a8722f8b3861e2058edcafde094ad059e152754986c3573306698f1";
    let tip_req = HttpRequestContents::new()
        .query_string(Some(query_txt_dup))
        .tip_request();
    let block_id =
        StacksBlockId::from_hex("03e26bd68a8722f8b3861e2058edcafde094ad059e152754986c3573306698f1")
            .unwrap();
    assert!(matches!(tip_req, TipRequest::SpecificTip(block_id)));

    // last parseable tip is taken
    let query_txt_dup = "tip=bad&tip=7070f213d719143d6045e08fd80f85014a161f8bbd3a42d1251576740826a392&tip=03e26bd68a8722f8b3861e2058edcafde094ad059e152754986c3573306698f1";
    let block_id =
        StacksBlockId::from_hex("03e26bd68a8722f8b3861e2058edcafde094ad059e152754986c3573306698f1")
            .unwrap();
    let tip_req = HttpRequestContents::new()
        .query_string(Some(query_txt_dup))
        .tip_request();
    assert!(matches!(tip_req, TipRequest::SpecificTip(block_id)));

    // tip can be skipped
    let query_txt_bad = "tip=bad";
    let tip_req = HttpRequestContents::new()
        .query_string(Some(query_txt_bad))
        .tip_request();
    assert_eq!(tip_req, TipRequest::UseLatestAnchoredTip);

    // tip can be skipped
    let query_txt_none = "tip=";
    let tip_req = HttpRequestContents::new()
        .query_string(Some(query_txt_none))
        .tip_request();
    assert_eq!(tip_req, TipRequest::UseLatestAnchoredTip);
}

#[test]
fn test_http_parse_cost_tracker_query() {
    // parses free cost tracker
    match HttpRequestContents::new()
        .query_string(Some("cost_tracker=free"))
        .get_cost_tracker()
    {
        CostTracker::Free => {}
        _ => panic!(),
    }

    // parses mid_block cost tracker
    match HttpRequestContents::new()
        .query_string(Some("cost_tracker=mid_block"))
        .get_cost_tracker()
    {
        CostTracker::MidBlock => {}
        _ => panic!(),
    }

    // defaults to mid block for malformed cost tracker
    match HttpRequestContents::new()
        .query_string(Some("cost_tracker=bad"))
        .get_cost_tracker()
    {
        CostTracker::MidBlock => {}
        _ => panic!(),
    }

    // defaults to mid block for missing cost tracker
    match HttpRequestContents::new()
        .query_string(Some("cost_tracker="))
        .get_cost_tracker()
    {
        CostTracker::MidBlock => {}
        _ => panic!(),
    }
}

#[test]
fn test_http_parse_proof_request_query() {
    let query_txt = "";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(proof_req);

    let query_txt = "proof=0";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(!proof_req);

    let query_txt = "proof=1";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(proof_req);

    let query_txt = "proof=0&proof=1";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(proof_req);

    let query_txt = "proof=1&proof=0";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(!proof_req);

    let query_txt = "proof=oops";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(!proof_req);

    let query_txt = "proof=oops&proof=1";
    let proof_req = HttpRequestContents::new()
        .query_string(Some(query_txt))
        .get_with_proof();
    assert!(proof_req);
}

#[test]
fn test_metrics_identifiers() {
    let convo = ConversationHttp::new(
        "127.0.0.1:12345".parse().unwrap(),
        None,
        PeerHost::DNS("localhost".to_string(), 12345),
        &ConnectionOptions::default(),
        100,
        32,
    );

    let fixtures = vec![
        // Valid requests
        (("GET", "/v2/info"), ("/v2/info", true)),
        (
            ("GET", "/v2/info?param1=value&param2=other_value"),
            ("/v2/info", true),
        ),
        (
            (
                "GET",
                "/v2/blocks/d8bd3c7e7cf7a9d783560a71356d3d9dbc84dc2f0c1a0001be8b141927c9d7ab",
            ),
            ("/v2/blocks/:block_id", true),
        ),
        // Invalid requests
        (("POST", "/v2/info"), ("<err-handler-not-found>", false)),
        (("GET", "!@#%&^$#!&^(@&+++"), ("<err-url-decode>", false)),
        (
            ("GET", "/some/nonexistent/endpoint"),
            ("<err-handler-not-found>", false),
        ),
        (
            (
                "GET",
                "/v2/blocks/dsviawevasigngawuqajauharpqjumzkalfuwgfkwpdhtbefgxkdhdfduskafdgh",
            ),
            ("<err-handler-not-found>", false),
        ),
    ];

    for (input, output) in fixtures {
        // Destructure fixture data
        let (verb, path_and_query_string) = input;
        let (metrics_identifier_expected, should_have_handler) = output;

        // Create request from data
        let preamble = HttpRequestPreamble::new(
            HttpVersion::Http11,
            verb.to_string(),
            path_and_query_string.to_string(),
            "localhost".to_string(),
            12345,
            true,
        );

        let mut request = StacksHttpRequest::new(preamble, HttpRequestContents::new());

        let metrics_identifier = convo.metrics_identifier(&mut request);
        let response_handler_index = request.get_response_handler_index();

        // Check that we get expected metrics identifier and request handler
        assert_eq!(metrics_identifier, metrics_identifier_expected);
        assert_eq!(response_handler_index.is_some(), should_have_handler);
    }
}

fn json_body(host: &str, port: u16, path: &str, json_bytes: &[u8]) -> StacksHttpRequest {
    let peerhost: PeerHost = format!("{host}:{port}")
        .parse()
        .unwrap_or(PeerHost::DNS(host.to_string(), port));
    let mut request = StacksHttpRequest::new_for_peer(
        peerhost,
        "POST".into(),
        path.into(),
        HttpRequestContents::new().payload_json(serde_json::from_slice(json_bytes).unwrap()),
    )
    .unwrap_or_else(|_| panic!("FATAL: failed to encode infallible data as HTTP request"));
    request.add_header("Connection".into(), "close".into());

    request
}

#[test]
fn test_send_request_timeout() {
    // Set up a TcpListener that accepts a connection but delays response
    let listener = TcpListener::bind("127.0.0.1:0").expect("Failed to bind test listener");
    let addr = listener.local_addr().unwrap();

    // Spawn a thread that will accept the connection and do nothing, simulating a long delay
    thread::spawn(move || {
        let (stream, _addr) = listener.accept().unwrap();
        // Hold the connection open to simulate a delay
        thread::sleep(Duration::from_secs(10));
        drop(stream); // Close the stream
    });

    // Set a timeout shorter than the sleep duration to force a timeout
    let connection_timeout = Duration::from_secs(2);

    // Attempt to connect, expecting a timeout error
    let result = send_http_request(
        "127.0.0.1",
        addr.port(),
        json_body("127.0.0.1", 80, "/", b"{}"),
        connection_timeout,
    );

    // Assert that the result is an error, specifically a timeout
    assert!(result.is_err(), "Expected a timeout error, got: {result:?}");

    if let Err(err) = result {
        assert_eq!(
            err.kind(),
            std::io::ErrorKind::WouldBlock,
            "Expected TimedOut error, got: {err:?}"
        );
    }
}

fn start_mock_server(response: String, client_done_signal: Receiver<()>) -> String {
    // Bind to an available port on localhost
    let listener = TcpListener::bind("127.0.0.1:0").expect("Failed to bind server");
    let addr = listener.local_addr().unwrap();

    debug!("Mock server listening on {}", addr);

    // Start the server in a new thread
    thread::spawn(move || {
        for stream in listener.incoming() {
            debug!("Mock server accepted connection");
            let mut stream = stream.expect("Failed to accept connection");

            // Read the client's request (even if we don't do anything with it)
            let mut buffer = [0; 512];
            let _ = stream.read(&mut buffer);
            debug!("Mock server received request");

            // Simulate a basic HTTP response
            stream
                .write_all(response.as_bytes())
                .expect("Failed to write response");
            stream.flush().expect("Failed to flush stream");
            debug!("Mock server sent response");

            // Wait for the client to signal that it's done reading
            client_done_signal
                .recv()
                .expect("Failed to receive client done signal");

            // Explicitly drop the stream after signaling to ensure the client finishes
            // NOTE: this will cause the test to slow down, since `send_http_request` expects
            // `Connection: close`
            drop(stream);

            debug!("Mock server closing connection");

            break; // Close after the first request
        }
    });

    // Return the address of the mock server
    format!("{}:{}", addr.ip(), addr.port())
}

fn parse_http_response(response: StacksHttpResponse) -> String {
    let response_txt = match response.destruct().1 {
        HttpResponsePayload::Text(s) => s,
        HttpResponsePayload::Empty => "".to_string(),
        HttpResponsePayload::JSON(js) => serde_json::to_string(&js).unwrap(),
        HttpResponsePayload::Bytes(bytes) => String::from_utf8_lossy(bytes.as_slice()).to_string(),
    };
    response_txt
}

#[test]
fn test_send_request_success() {
    // Prepare the mock server to return a successful HTTP response
    let mock_response = "HTTP/1.1 200 OK\r\nContent-Length: 13\r\n\r\nHello, world!";

    // Create a channel to signal when the client is done reading
    let (tx_client_done, rx_client_done) = channel();
    let server_addr = start_mock_server(mock_response.to_string(), rx_client_done);
    let timeout_duration = Duration::from_secs(5);

    let parts = server_addr.split(':').collect::<Vec<&str>>();
    let host = parts[0];
    let port = parts[1].parse().unwrap();

    // Attempt to send a request to the mock server
    let result = send_http_request(
        host,
        port,
        json_body(host, port, "/", b"{}"),
        timeout_duration,
    );
    debug!("Got result: {result:?}");

    // Ensure the server only closes after the client has finished processing
    if let Ok(response) = &result {
        let body = parse_http_response(response.clone());
        assert_eq!(body, "Hello, world!", "Unexpected response body: {body}");
    }

    tx_client_done
        .send(())
        .expect("Failed to send close signal");

    // Assert that the connection was successful
    assert!(
        result.is_ok(),
        "Expected a successful request, but got {result:?}"
    );
}
