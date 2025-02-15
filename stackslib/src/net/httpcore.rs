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

/// This module binds the http library to Stacks as a `ProtocolFamily` implementation
use std::collections::{BTreeMap, HashMap};
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpStream, ToSocketAddrs};
use std::time::{Duration, Instant};
use std::{fmt, io, mem};

use clarity::vm::costs::ExecutionCost;
use clarity::vm::types::{QualifiedContractIdentifier, BOUND_VALUE_SERIALIZATION_HEX};
use clarity::vm::{ClarityName, ContractName};
use percent_encoding::percent_decode_str;
use regex::{Captures, Regex};
use stacks_common::codec::{read_next, Error as CodecError, StacksMessageCodec, MAX_MESSAGE_LEN};
use stacks_common::types::chainstate::{
    ConsensusHash, StacksAddress, StacksBlockId, StacksPublicKey,
};
use stacks_common::types::net::PeerHost;
use stacks_common::types::Address;
use stacks_common::util::chunked_encoding::*;
use stacks_common::util::retry::{BoundReader, RetryReader};
use stacks_common::util::{get_epoch_time_ms, get_epoch_time_secs};
use url::Url;

use super::rpc::ConversationHttp;
use crate::burnchains::Txid;
use crate::chainstate::burn::db::sortdb::SortitionDB;
use crate::chainstate::burn::BlockSnapshot;
use crate::chainstate::nakamoto::NakamotoChainState;
use crate::chainstate::stacks::db::{StacksChainState, StacksHeaderInfo};
use crate::core::{MemPoolDB, StacksEpoch};
use crate::net::connection::{ConnectionOptions, NetworkConnection};
use crate::net::http::common::{parse_raw_bytes, HTTP_PREAMBLE_MAX_ENCODED_SIZE};
use crate::net::http::{
    http_reason, parse_bytes, parse_json, Error as HttpError, HttpBadRequest, HttpContentType,
    HttpErrorResponse, HttpNotFound, HttpRequest, HttpRequestContents, HttpRequestPreamble,
    HttpResponse, HttpResponseContents, HttpResponsePayload, HttpResponsePreamble, HttpServerError,
    HttpVersion,
};
use crate::net::p2p::PeerNetwork;
use crate::net::server::HttpPeer;
use crate::net::{Error as NetError, MessageSequence, ProtocolFamily, StacksNodeState, UrlString};

const CHUNK_BUF_LEN: usize = 32768;

/// canonical stacks tip height header
pub const STACKS_HEADER_HEIGHT: &str = "X-Canonical-Stacks-Tip-Height";

/// request ID header
pub const STACKS_REQUEST_ID: &str = "X-Request-Id";

/// Request ID to use or expect from non-Stacks HTTP clients.
/// In particular, if a HTTP response does not contain the x-request-id header, then it's assumed
/// to be this value.  This is needed to support fetching immutables like block and microblock data
/// from non-Stacks nodes (like Gaia hubs, CDNs, vanilla HTTP servers, and so on).
pub const HTTP_REQUEST_ID_RESERVED: u32 = 0;

/// All representations of the `tip=` query parameter value
#[derive(Debug, Clone, PartialEq)]
pub enum TipRequest {
    UseLatestAnchoredTip,
    UseLatestUnconfirmedTip,
    SpecificTip(StacksBlockId),
}

impl TipRequest {}

impl fmt::Display for TipRequest {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UseLatestAnchoredTip => write!(f, ""),
            Self::UseLatestUnconfirmedTip => write!(f, "latest"),
            Self::SpecificTip(ref tip) => write!(f, "{tip}"),
        }
    }
}

impl From<&str> for TipRequest {
    fn from(s: &str) -> TipRequest {
        if s == "latest" {
            TipRequest::UseLatestUnconfirmedTip
        } else if let Ok(block_id) = StacksBlockId::from_hex(s) {
            TipRequest::SpecificTip(block_id)
        } else {
            TipRequest::UseLatestAnchoredTip
        }
    }
}

/// All representations of the `cost_tracker=` query parameter value;
/// Each value corresponds to a different choice of construction of a cost tracker
/// (implementing clarity::vm::costs::CostTracker).
#[derive(Debug, Clone, PartialEq)]
pub enum CostTracker {
    /// Use LimitedCostTracker::Free
    Free,
    /// Use LimitedCostTracker:new_mid_block
    MidBlock,
}

impl fmt::Display for CostTracker {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Free => write!(f, "free"),
            Self::MidBlock => write!(f, "mid_block"),
        }
    }
}

impl From<&str> for CostTracker {
    fn from(s: &str) -> CostTracker {
        match s {
            "free" => CostTracker::Free,
            "mid_block" => CostTracker::MidBlock,
            _ => CostTracker::MidBlock,
        }
    }
}

/// Extension to HttpRequestPreamble to give it awareness of Stacks-specific fields
pub trait HttpPreambleExtensions {
    /// Set the node's canonical Stacks chain tip
    fn set_canonical_stacks_tip_height(&mut self, height: Option<u32>);
    /// Set the node's request ID
    fn set_request_id(&mut self, req_id: u32);
    /// Get the canonical stacks chain tip
    fn get_canonical_stacks_tip_height(&self) -> Option<u32>;
    /// Get the request ID
    fn get_request_id(&self) -> Option<u32>;
}

impl HttpPreambleExtensions for HttpRequestPreamble {
    /// Set the canonical Stacks chain tip height
    fn set_canonical_stacks_tip_height(&mut self, height_opt: Option<u32>) {
        if let Some(height) = height_opt {
            self.add_header(
                "X-Canonical-Stacks-Tip-Height".into(),
                format!("{}", &height),
            );
        } else {
            self.remove_header("X-Canonical-Stacks-Tip-Height".to_string());
        }
    }

    /// Set the request ID
    fn set_request_id(&mut self, id: u32) {
        self.add_header("X-Request-Id".into(), format!("{}", id));
    }

    /// Get the canonical Stacks chain tip
    fn get_canonical_stacks_tip_height(&self) -> Option<u32> {
        self.get_header("X-Canonical-Stacks-Tip-Height".to_string())
            .and_then(|hdr| hdr.parse::<u32>().ok())
    }

    /// Get the request ID
    fn get_request_id(&self) -> Option<u32> {
        self.get_header("X-Request-Id".to_string())
            .and_then(|req| req.parse::<u32>().ok())
    }
}

impl HttpPreambleExtensions for HttpResponsePreamble {
    /// Set the canonical Stacks chain tip height
    fn set_canonical_stacks_tip_height(&mut self, height_opt: Option<u32>) {
        if let Some(height) = height_opt {
            self.add_header(
                "X-Canonical-Stacks-Tip-Height".into(),
                format!("{}", &height),
            );
        } else {
            self.remove_header("X-Canonical-Stacks-Tip-Height".to_string());
        }
    }

    /// Set the request ID
    fn set_request_id(&mut self, id: u32) {
        self.add_header("X-Request-Id".into(), format!("{}", id));
    }

    /// Get the canonical Stacks chain tip
    fn get_canonical_stacks_tip_height(&self) -> Option<u32> {
        self.get_header("X-Canonical-Stacks-Tip-Height".to_string())
            .and_then(|hdr| hdr.parse::<u32>().ok())
    }

    /// Get the request ID
    fn get_request_id(&self) -> Option<u32> {
        self.get_header("X-Request-Id".to_string())
            .and_then(|req| req.parse::<u32>().ok())
    }
}

/// This module contains request helpers for decoding common data found in the request path regex captures.
/// The error types convert to HTTP responses.
pub mod request {
    use super::*;

    /// Get and parse a contract address from a path's captures, given the address and contract
    /// regex field names.
    pub fn get_contract_address(
        captures: &Captures,
        address_key: &str,
        contract_key: &str,
    ) -> Result<QualifiedContractIdentifier, HttpError> {
        let address = if let Some(address_str) = captures.name(address_key) {
            if let Some(addr) = StacksAddress::from_string(address_str.as_str()) {
                addr
            } else {
                return Err(HttpError::Http(
                    400,
                    format!("Failed to decode `{}`", address_key),
                ));
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", address_key)));
        };

        let contract_name = if let Some(contract_str) = captures.name(contract_key) {
            if let Ok(contract_name) = ContractName::try_from(contract_str.as_str().to_string()) {
                contract_name
            } else {
                return Err(HttpError::Http(
                    400,
                    format!("Failed to decode `{}`", contract_key),
                ));
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", contract_key)));
        };

        let contract_identifier = QualifiedContractIdentifier::new(address.into(), contract_name);

        Ok(contract_identifier)
    }

    /// Get and parse a StacksBlockId from a path's captures, given the name of the regex field.
    pub fn get_block_hash(captures: &Captures, key: &str) -> Result<StacksBlockId, HttpError> {
        let block_id = if let Some(block_id) = captures.name(key) {
            match StacksBlockId::from_hex(block_id.as_str()) {
                Ok(bhh) => bhh,
                Err(_e) => {
                    return Err(HttpError::Http(400, format!("Failed to decode `{}`", key)));
                }
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", key)));
        };
        Ok(block_id)
    }

    /// Get and parse a Txid from a path's captures, given the name of the regex field.
    pub fn get_txid(captures: &Captures, key: &str) -> Result<Txid, HttpError> {
        let txid = if let Some(txid) = captures.name(key) {
            match Txid::from_hex(txid.as_str()) {
                Ok(bhh) => bhh,
                Err(_e) => {
                    return Err(HttpError::Http(400, format!("Failed to decode `{}`", key)));
                }
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", key)));
        };
        Ok(txid)
    }

    /// Get and parse a Clarity name from a path's captures, given the name of the regex field.
    pub fn get_clarity_name(captures: &Captures, key: &str) -> Result<ClarityName, HttpError> {
        let clarity_name = if let Some(name_str) = captures.name(key) {
            if let Ok(clarity_name) = ClarityName::try_from(name_str.as_str().to_string()) {
                clarity_name
            } else {
                return Err(HttpError::Http(400, format!("Failed to decode `{}`", key)));
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", key)));
        };

        Ok(clarity_name)
    }

    /// Get and parse a ConsensusHash from a path's captures, given the name of the regex field.
    pub fn get_consensus_hash(captures: &Captures, key: &str) -> Result<ConsensusHash, HttpError> {
        let ch = if let Some(ch_str) = captures.name(key) {
            match ConsensusHash::from_hex(ch_str.as_str()) {
                Ok(ch) => ch,
                Err(_e) => {
                    return Err(HttpError::Http(400, format!("Failed to decode `{}`", key)));
                }
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", key)));
        };
        Ok(ch)
    }

    /// Get and parse a u32 from a path's captures, given the name of the regex field.
    pub fn get_u32(captures: &Captures, key: &str) -> Result<u32, HttpError> {
        let u = if let Some(u32_str) = captures.name(key) {
            match u32_str.as_str().parse::<u32>() {
                Ok(x) => x,
                Err(_e) => {
                    return Err(HttpError::Http(400, format!("Failed to decode `{}`", key)));
                }
            }
        } else {
            return Err(HttpError::Http(404, format!("Missing `{}`", key)));
        };
        Ok(u)
    }
}

/// Extension to HttpRequestContents to give it awareness of Stacks-specific fields
pub trait HttpRequestContentsExtensions {
    /// Chain constructor: Request a specific tip
    fn for_specific_tip(self, tip: StacksBlockId) -> Self;
    /// Chain constructor: use a given TipRequest
    fn for_tip(self, tip_req: TipRequest) -> Self;
    /// Identify the tip request
    fn tip_request(&self) -> TipRequest;
    /// Identify the cost tracker (e.g. when executing a contract)
    fn get_cost_tracker(&self) -> CostTracker;
    /// Determine if we should return a MARF proof
    fn get_with_proof(&self) -> bool;
}

impl HttpRequestContentsExtensions for HttpRequestContents {
    /// Request a specific tip
    fn for_specific_tip(self, tip: StacksBlockId) -> Self {
        self.query_arg("tip".to_string(), format!("{}", &tip))
    }

    /// Use a particular tip request
    fn for_tip(mut self, tip_req: TipRequest) -> Self {
        if tip_req != TipRequest::UseLatestAnchoredTip {
            self.query_arg("tip".to_string(), tip_req.to_string())
        } else {
            let _ = self.take_query_arg(&"tip".to_string());
            self
        }
    }

    /// Ref the tip request
    fn tip_request(&self) -> TipRequest {
        self.get_query_args()
            .get("tip")
            .map(|tip| tip.as_str().into())
            .unwrap_or(TipRequest::UseLatestAnchoredTip)
    }

    // Get the cost_tracker= query parameter value
    fn get_cost_tracker(&self) -> CostTracker {
        self.get_query_args()
            .get("cost_tracker")
            .map(|cost_tracker| cost_tracker.as_str().into())
            .unwrap_or(CostTracker::MidBlock)
    }

    /// Get the proof= query parameter value
    fn get_with_proof(&self) -> bool {
        let proof_value = self
            .get_query_arg("proof")
            .map(|x| x.to_owned())
            // default to "with proof"
            .unwrap_or("1".into());
        &proof_value == "1"
    }
}

/// Work around Clone blanket implementations not being object-safe
pub trait RPCRequestHandlerClone {
    fn clone_rpc_handler_box(&self) -> Box<dyn RPCRequestHandler>;
}

impl<T> RPCRequestHandlerClone for T
where
    T: 'static + RPCRequestHandler + Clone,
{
    fn clone_rpc_handler_box(&self) -> Box<dyn RPCRequestHandler> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn RPCRequestHandler> {
    fn clone(&self) -> Box<dyn RPCRequestHandler> {
        self.clone_rpc_handler_box()
    }
}

/// Trait that every HTTP round-trip request type must implement.
pub trait RPCRequestHandler: HttpRequest + HttpResponse + RPCRequestHandlerClone {
    /// Reset the RPC handler.  This clears any internal state this handler stored between calls to
    /// `try_handle_request()`
    fn restart(&mut self);
    /// Instantiate the HTTP response headers and body from a request
    fn try_handle_request(
        &mut self,
        request_preamble: HttpRequestPreamble,
        request_body: HttpRequestContents,
        state: &mut StacksNodeState,
    ) -> Result<(HttpResponsePreamble, HttpResponseContents), NetError>;

    /// Helper to get the canonical sortition tip
    fn get_canonical_burn_chain_tip(
        &self,
        preamble: &HttpRequestPreamble,
        sortdb: &SortitionDB,
    ) -> Result<BlockSnapshot, StacksHttpResponse> {
        SortitionDB::get_canonical_burn_chain_tip(sortdb.conn()).map_err(|e| {
            StacksHttpResponse::new_error(
                preamble,
                &HttpServerError::new(format!("Failed to load canonical burnchain tip: {:?}", &e)),
            )
        })
    }

    /// Helper to get the current Stacks epoch
    fn get_stacks_epoch(
        &self,
        preamble: &HttpRequestPreamble,
        sortdb: &SortitionDB,
        block_height: u64,
    ) -> Result<StacksEpoch, StacksHttpResponse> {
        SortitionDB::get_stacks_epoch(sortdb.conn(), block_height)
            .map_err(|e| {
                StacksHttpResponse::new_error(preamble, &HttpServerError::new(format!("Could not load Stacks epoch for canonical burn height: {:?}", &e)))
            })?
            .ok_or_else(|| {
                let msg = format!(
                    "Failed to get fee rate estimate because could not load Stacks epoch for canonical burn height = {}",
                    block_height
                );
                warn!("{}", &msg);
                StacksHttpResponse::new_error(preamble, &HttpServerError::new(msg))
            })
    }

    /// Helper to get the Stacks tip
    fn get_stacks_chain_tip(
        &self,
        preamble: &HttpRequestPreamble,
        sortdb: &SortitionDB,
        chainstate: &StacksChainState,
    ) -> Result<StacksHeaderInfo, StacksHttpResponse> {
        NakamotoChainState::get_canonical_block_header(chainstate.db(), sortdb)
            .map_err(|e| {
                let msg = format!("Failed to load stacks chain tip header: {:?}", &e);
                warn!("{}", &msg);
                StacksHttpResponse::new_error(preamble, &HttpServerError::new(msg))
            })?
            .ok_or_else(|| {
                let msg =
                    "No stacks tip exists yet. Perhaps no blocks have been processed by this node"
                        .to_string();
                warn!("{}", &msg);
                StacksHttpResponse::new_error(preamble, &HttpNotFound::new(msg))
            })
    }
}

/// A decoded HttpRequest for use in Stacks
#[derive(Debug, Clone, PartialEq)]
pub struct StacksHttpRequest {
    preamble: HttpRequestPreamble,
    contents: HttpRequestContents,
    start_time: u128,
    /// Cache result of `StacksHttp::find_response_handler` so we don't have to do the regex matching twice
    response_handler_index: Option<usize>,
}

impl StacksHttpRequest {
    pub fn new(preamble: HttpRequestPreamble, contents: HttpRequestContents) -> Self {
        Self {
            preamble,
            contents,
            start_time: get_epoch_time_ms(),
            response_handler_index: None,
        }
    }

    /// Instantiate a request to a remote Stacks peer
    /// `path` is just the request path.  Query arguments are added via `contents`.  Any query
    /// component to `path` will be silently dropped.
    ///
    /// In Stacks, all requests must have a known content length.  If it cannot be calculated, then
    /// this method will fail.
    pub fn new_for_peer(
        peerhost: PeerHost,
        verb: String,
        path: String,
        contents: HttpRequestContents,
    ) -> Result<Self, NetError> {
        let mut preamble = HttpRequestPreamble::new_for_peer(peerhost, verb, path);
        if let Some(ct) = contents.content_type() {
            preamble.set_content_type(ct);
        }
        let content_length = contents.content_length()?;
        if content_length > 0 || contents.content_type().is_some() {
            preamble.set_content_length(content_length);
        }
        let (decoded_path, _) = decode_request_path(&preamble.path_and_query_str)?;
        let full_query_string = contents.get_full_query_string();
        preamble.path_and_query_str = if full_query_string.is_empty() {
            decoded_path
        } else {
            format!("{decoded_path}?{full_query_string}")
        };

        Ok(Self {
            preamble,
            contents,
            start_time: get_epoch_time_ms(),
            response_handler_index: None,
        })
    }

    /// Get a reference to the request premable metadata
    pub fn preamble(&self) -> &HttpRequestPreamble {
        &self.preamble
    }

    /// Get a mutable reference to the request premable metadata
    pub fn preamble_mut(&mut self) -> &mut HttpRequestPreamble {
        &mut self.preamble
    }

    /// Get a reference to the request contents
    pub fn contents(&self) -> &HttpRequestContents {
        &self.contents
    }

    /// Get a reference to the fully-qualified request path
    pub fn request_path(&self) -> &str {
        &self.preamble.path_and_query_str
    }

    /// Get the HTTP verb for this request
    pub fn verb(&self) -> &str {
        &self.preamble.verb
    }

    /// Get the number of milliseconds elapsed since this request was created
    pub fn duration_ms(&self) -> u128 {
        let now = get_epoch_time_ms();
        now.saturating_sub(self.start_time)
    }

    /// Write out this message to a Write.
    /// NOTE: In practice, the Write will be a reply handle endpoint, so writing to it won't block.
    pub fn send<W: Write>(&self, fd: &mut W) -> Result<(), NetError> {
        self.preamble.send(fd)?;
        self.contents.get_payload().send(fd).map_err(NetError::from)
    }

    /// Add a request header
    pub fn add_header(&mut self, hdr: String, value: String) {
        self.preamble.add_header(hdr, value);
    }

    /// Constructor to add headers
    pub fn with_header(mut self, hdr: String, value: String) -> Self {
        self.add_header(hdr, value);
        self
    }

    /// Get a ref to all request headers
    pub fn get_headers(&self) -> &BTreeMap<String, String> {
        &self.preamble.headers
    }

    /// Clear all extra headers
    pub fn clear_headers(&mut self) {
        self.preamble.headers.clear();
    }

    /// Destruct into parts
    pub fn destruct(self) -> (HttpRequestPreamble, HttpRequestContents) {
        (self.preamble, self.contents)
    }

    #[cfg(test)]
    pub fn try_serialize(&self) -> Result<Vec<u8>, NetError> {
        let mut ret = vec![];
        self.send(&mut ret)?;
        Ok(ret)
    }

    #[cfg(test)]
    pub fn get_response_handler_index(&self) -> Option<usize> {
        self.response_handler_index
    }
}

/// A received HTTP response (fully decoded in RAM)
#[derive(Debug, Clone, PartialEq)]
pub struct StacksHttpResponse {
    /// Information about the response (e.g. headers and header-derived data)
    preamble: HttpResponsePreamble,
    /// The body contents
    body: HttpResponsePayload,
}

impl From<StacksHttpResponse> for Result<(HttpResponsePreamble, HttpResponseContents), NetError> {
    fn from(resp: StacksHttpResponse) -> Self {
        resp.try_into_contents()
    }
}

impl StacksHttpResponse {
    pub fn new(preamble: HttpResponsePreamble, body: HttpResponsePayload) -> StacksHttpResponse {
        StacksHttpResponse { preamble, body }
    }

    pub fn preamble(&self) -> &HttpResponsePreamble {
        &self.preamble
    }

    pub fn body(&self) -> &HttpResponsePayload {
        &self.body
    }

    pub fn destruct(self) -> (HttpResponsePreamble, HttpResponsePayload) {
        (self.preamble, self.body)
    }

    /// Convert into an HTTP response so an HttpRequest impl can return it
    pub fn try_into_contents(
        self,
    ) -> Result<(HttpResponsePreamble, HttpResponseContents), NetError> {
        Ok((self.preamble, self.body.try_into()?))
    }

    /// Send this HTTP response on a given Write.  Only used for testing; in practice, the RPC
    /// request handler takes care of sending or streaming data back.
    pub fn send<W: Write>(&self, fd: &mut W) -> Result<(), NetError> {
        self.preamble.consensus_serialize(fd)?;
        if self.preamble.content_length.is_some() {
            self.body.send(fd).map_err(NetError::from)
        } else {
            self.body
                .send_chunked(CHUNK_BUF_LEN, fd)
                .map_err(NetError::from)
        }
    }

    /// Make a new HTTP error response, in reaction to a request
    pub fn new_error(
        preamble: &HttpRequestPreamble,
        error: &dyn HttpErrorResponse,
    ) -> StacksHttpResponse {
        let payload = error.payload();
        let content_type = match &payload {
            HttpResponsePayload::Empty => HttpContentType::Bytes,
            HttpResponsePayload::Bytes(..) => HttpContentType::Bytes,
            HttpResponsePayload::Text(..) => HttpContentType::Text,
            HttpResponsePayload::JSON(..) => HttpContentType::JSON,
        };
        let content_length = payload.try_content_length();
        let preamble = HttpResponsePreamble::from_http_request_preamble(
            preamble,
            error.code(),
            http_reason(error.code()),
            content_length,
            content_type,
        );
        StacksHttpResponse::new(preamble, payload)
    }

    /// Make a new HTTP error response for text, apropos of nothing
    pub fn new_empty_error(error: &dyn HttpErrorResponse) -> StacksHttpResponse {
        let code = error.code();
        let payload = error.payload();
        let reason = http_reason(code);
        let preamble = match &payload {
            HttpResponsePayload::Empty => HttpResponsePreamble::error_bytes(code, reason),
            HttpResponsePayload::Bytes(..) => HttpResponsePreamble::error_bytes(code, reason),
            HttpResponsePayload::JSON(..) => HttpResponsePreamble::error_json(code, reason),
            HttpResponsePayload::Text(ref txt) => {
                HttpResponsePreamble::error_text(code, reason, txt)
            }
        };

        StacksHttpResponse::new(preamble, payload)
    }

    /// Get the internal payload if the HTTP response was 200.
    /// If it was 404, return NotFoundError
    /// Otherwise, if it was not 200, return RecvError
    pub fn get_http_payload_ok(self) -> Result<HttpResponsePayload, NetError> {
        let (preamble, payload) = self.destruct();
        if preamble.status_code == 404 {
            return Err(NetError::NotFoundError);
        }

        if preamble.status_code != 200 {
            return Err(NetError::RecvError(format!(
                "HTTP status {}",
                &preamble.status_code
            )));
        }

        Ok(payload)
    }

    /// Clear all extra headers
    pub fn clear_headers(&mut self) {
        self.preamble.headers.clear();
    }

    #[cfg(test)]
    pub fn try_serialize(&self) -> Result<Vec<u8>, NetError> {
        let mut ret = vec![];
        self.send(&mut ret)?;
        Ok(ret)
    }
}

/// Message type for HTTP
#[derive(Debug, Clone, PartialEq)]
pub enum StacksHttpMessage {
    Request(StacksHttpRequest),
    Response(StacksHttpResponse),
    Error(String, StacksHttpResponse),
}

/// HTTP message preamble
#[derive(Debug, Clone, PartialEq)]
pub enum StacksHttpPreamble {
    Request(HttpRequestPreamble),
    Response(HttpResponsePreamble),
}

impl StacksHttpPreamble {
    #[cfg(test)]
    pub fn expect_request(self) -> HttpRequestPreamble {
        match self {
            Self::Request(x) => x,
            _ => panic!("Not a request preamble"),
        }
    }

    #[cfg(test)]
    pub fn expect_response(self) -> HttpResponsePreamble {
        match self {
            Self::Response(x) => x,
            _ => panic!("Not a response preamble"),
        }
    }
}

impl StacksMessageCodec for StacksHttpPreamble {
    fn consensus_serialize<W: Write>(&self, fd: &mut W) -> Result<(), CodecError> {
        match *self {
            StacksHttpPreamble::Request(ref req) => req.consensus_serialize(fd),
            StacksHttpPreamble::Response(ref res) => res.consensus_serialize(fd),
        }
    }

    fn consensus_deserialize<R: Read>(fd: &mut R) -> Result<StacksHttpPreamble, CodecError> {
        let mut retry_fd = RetryReader::new(fd);

        // the byte stream can decode to a http request or a http response, but not both.
        match HttpRequestPreamble::consensus_deserialize(&mut retry_fd) {
            Ok(request) => Ok(StacksHttpPreamble::Request(request)),
            Err(e_request) => {
                // maybe a http response?
                retry_fd.set_position(0);
                match HttpResponsePreamble::consensus_deserialize(&mut retry_fd) {
                    Ok(response) => Ok(StacksHttpPreamble::Response(response)),
                    Err(e) => {
                        // underflow?
                        match (e_request, e) {
                            (CodecError::ReadError(ref ioe1), CodecError::ReadError(ref ioe2)) => {
                                if ioe1.kind() == io::ErrorKind::UnexpectedEof && ioe2.kind() == io::ErrorKind::UnexpectedEof {
                                    // out of bytes
                                    Err(CodecError::UnderflowError("Not enough bytes to form a HTTP request or response".to_string()))
                                }
                                else {
                                    Err(CodecError::DeserializeError(format!("Neither a HTTP request ({:?}) or HTTP response ({:?})", ioe1, ioe2)))
                                }
                            },
                            (e_req, e_res) => Err(CodecError::DeserializeError(format!("Failed to decode HTTP request or HTTP response (request error: {:?}; response error: {:?})", &e_req, &e_res)))
                        }
                    }
                }
            }
        }
    }
}

impl MessageSequence for StacksHttpMessage {
    fn request_id(&self) -> u32 {
        // there is at most one in-flight HTTP request, as far as a Connection<P> is concerned
        HTTP_REQUEST_ID_RESERVED
    }

    fn get_message_name(&self) -> &'static str {
        "StacksHttpMessage"
    }
}

/// A partially-decoded, streamed HTTP message (response) being received.
/// Internally used by StacksHttp to keep track of chunk-decoding state.
#[derive(Debug, Clone, PartialEq)]
struct StacksHttpRecvStream {
    state: HttpChunkedTransferReaderState,
    data: Vec<u8>,
    total_consumed: usize, // number of *encoded* bytes consumed
}

impl StacksHttpRecvStream {
    pub fn new(max_size: u64) -> StacksHttpRecvStream {
        StacksHttpRecvStream {
            state: HttpChunkedTransferReaderState::new(max_size),
            data: vec![],
            total_consumed: 0,
        }
    }

    /// Feed data into our chunked transfer reader state.  If we finish reading a stream, return
    /// the decoded bytes (as Some(Vec<u8>) and the total number of encoded bytes consumed).
    /// Always returns the number of bytes consumed.
    pub fn consume_data<R: Read>(
        &mut self,
        fd: &mut R,
    ) -> Result<(Option<(Vec<u8>, usize)>, usize), NetError> {
        let mut consumed = 0;
        let mut blocked = false;
        while !blocked {
            let mut decoded_buf = vec![0u8; CHUNK_BUF_LEN];
            let (read_pass, consumed_pass) = match self.state.do_read(fd, &mut decoded_buf) {
                Ok((0, num_consumed)) => {
                    test_debug!(
                        "consume_data blocked on 0 decoded bytes ({} consumed)",
                        num_consumed
                    );
                    blocked = true;
                    (0, num_consumed)
                }
                Ok((num_read, num_consumed)) => {
                    test_debug!(
                        "consume_data read {} bytes ({} consumed)",
                        num_read,
                        num_consumed
                    );
                    (num_read, num_consumed)
                }
                Err(e) => {
                    if e.kind() == io::ErrorKind::WouldBlock || e.kind() == io::ErrorKind::TimedOut
                    {
                        test_debug!("consume_data blocked on read error");
                        blocked = true;
                        (0, 0)
                    } else {
                        return Err(NetError::ReadError(e));
                    }
                }
            };

            consumed += consumed_pass;
            if read_pass > 0 {
                self.data.extend_from_slice(&decoded_buf[0..read_pass]);
            }
        }

        self.total_consumed += consumed;

        // did we get a message?
        if self.state.is_eof() {
            // reset
            let message_data = mem::replace(&mut self.data, vec![]);
            let total_consumed = self.total_consumed;

            self.state = HttpChunkedTransferReaderState::new(self.state.max_size);
            self.total_consumed = 0;

            Ok((Some((message_data, total_consumed)), consumed))
        } else {
            Ok((None, consumed))
        }
    }
}

/// Information about an in-flight request
#[derive(Debug, Clone, PartialEq)]
struct StacksHttpReplyData {
    request_id: u32,
    stream: StacksHttpRecvStream,
}

/// Default response handler, for when using StacksHttp to issue arbitrary requests
#[derive(Clone)]
struct RPCArbitraryResponseHandler {}
impl HttpResponse for RPCArbitraryResponseHandler {
    fn try_parse_response(
        &self,
        preamble: &HttpResponsePreamble,
        body: &[u8],
    ) -> Result<HttpResponsePayload, HttpError> {
        match preamble.content_type {
            HttpContentType::Bytes => {
                let bytes = parse_bytes(preamble, body, MAX_MESSAGE_LEN.into())?;
                Ok(HttpResponsePayload::Bytes(bytes))
            }
            HttpContentType::JSON => {
                if body.len() > MAX_MESSAGE_LEN as usize {
                    return Err(HttpError::DecodeError(
                        "Message is too long to decode".into(),
                    ));
                }

                let json = parse_json(preamble, body)?;
                Ok(HttpResponsePayload::JSON(json))
            }
            HttpContentType::Text => {
                let text_bytes = parse_raw_bytes(
                    preamble,
                    body,
                    MAX_MESSAGE_LEN.into(),
                    HttpContentType::Text,
                )?;
                let text = String::from_utf8_lossy(&text_bytes).to_string();
                Ok(HttpResponsePayload::Text(text))
            }
        }
    }
}

/// Stacks HTTP state machine implementation, for bufferring up data.
/// One of these exists per Connection<P: Protocol>.
/// There can be at most one HTTP request in-flight (i.e. we don't do pipelining).
///
/// This state machine gets used for both clients and servers.  A client issues an HTTP request,
/// and must receive a follow-up HTTP reply (or the state machine errors out).  A server receives
/// an HTTP request, and sends an HTTP reply.
#[derive(Clone)]
pub struct StacksHttp {
    /// Address of peer
    peer_addr: SocketAddr,
    /// offset body after '\r\n\r\n' if known
    body_start: Option<usize>,
    /// number of preamble bytes seen so far
    num_preamble_bytes: usize,
    /// last 4 bytes of the preamble we've seen, just in case the \r\n\r\n straddles two calls to
    /// read_preamble()
    last_four_preamble_bytes: [u8; 4],
    /// Incoming reply state
    reply: Option<StacksHttpReplyData>,
    /// Size of HTTP chunks to write
    chunk_size: usize,
    /// Which request handler is active.
    /// This is only used if this state-machine is used by a client to issue a request and then
    /// parse a reply.  If instead this state-machine is used by the server to parse a request and
    /// send a reply, it will be unused.
    request_handler_index: Option<usize>,
    /// HTTP request handlers (verb, regex, request-handler, response-handler)
    request_handlers: Vec<(String, Regex, Box<dyn RPCRequestHandler>)>,
    /// Maximum size of call arguments
    pub maximum_call_argument_size: u32,
    /// Maximum execution budget of a read-only call
    pub read_only_call_limit: ExecutionCost,
    /// The authorization token to enable access to privileged features, such as the block proposal RPC endpoint
    pub auth_token: Option<String>,
    /// Allow arbitrary responses to be handled in addition to request handlers
    allow_arbitrary_response: bool,
}

impl StacksHttp {
    /// Create an HTTP protocol state machine that handles the built-in RPC API.
    /// Used for building the RPC server
    pub fn new(peer_addr: SocketAddr, conn_opts: &ConnectionOptions) -> StacksHttp {
        let mut http = StacksHttp {
            peer_addr,
            body_start: None,
            num_preamble_bytes: 0,
            last_four_preamble_bytes: [0u8; 4],
            reply: None,
            chunk_size: 8192,
            request_handler_index: None,
            request_handlers: vec![],
            maximum_call_argument_size: conn_opts.maximum_call_argument_size,
            read_only_call_limit: conn_opts.read_only_call_limit.clone(),
            auth_token: conn_opts.auth_token.clone(),
            allow_arbitrary_response: false,
        };
        http.register_rpc_methods();
        http
    }

    /// Create an HTTP protocol state machine that can handle arbitrary responses.
    /// Used for building clients.
    pub fn new_client(peer_addr: SocketAddr, conn_opts: &ConnectionOptions) -> StacksHttp {
        StacksHttp {
            peer_addr,
            body_start: None,
            num_preamble_bytes: 0,
            last_four_preamble_bytes: [0u8; 4],
            reply: None,
            chunk_size: 8192,
            request_handler_index: None,
            request_handlers: vec![],
            maximum_call_argument_size: conn_opts.maximum_call_argument_size,
            read_only_call_limit: conn_opts.read_only_call_limit.clone(),
            auth_token: conn_opts.auth_token.clone(),
            allow_arbitrary_response: true,
        }
    }

    /// Register an API RPC endpoint
    pub fn register_rpc_endpoint<Handler: RPCRequestHandler + 'static>(
        &mut self,
        handler: Handler,
    ) {
        self.request_handlers.push((
            handler.verb().to_string(),
            handler.path_regex(),
            Box::new(handler),
        ));
    }

    /// Find the HTTP request handler to use to process the reply, given the request path.
    /// Returns the index into the list of handlers
    fn find_response_handler(&self, request_verb: &str, request_path: &str) -> Option<usize> {
        for (i, (verb, regex, _)) in self.request_handlers.iter().enumerate() {
            if request_verb != verb {
                continue;
            }
            let Some(_captures) = regex.captures(request_path) else {
                continue;
            };

            return Some(i);
        }
        None
    }

    /// Force the state machine to expect a response
    #[cfg(test)]
    pub fn set_response_handler(&mut self, request_verb: &str, request_path: &str) {
        let handler_index = self
            .find_response_handler(request_verb, request_path)
            .unwrap_or_else(|| {
                panic!("FATAL: could not find handler for '{request_verb}' '{request_path}'")
            });
        self.request_handler_index = Some(handler_index);
    }

    /// Try to parse an inbound HTTP request using a given handler, preamble, and body
    #[cfg(test)]
    pub fn handle_try_parse_request(
        &self,
        handler: &mut dyn RPCRequestHandler,
        preamble: &HttpRequestPreamble,
        body: &[u8],
    ) -> Result<StacksHttpRequest, NetError> {
        let (decoded_path, query) = decode_request_path(&preamble.path_and_query_str)?;
        let captures = if let Some(caps) = handler.path_regex().captures(&decoded_path) {
            caps
        } else {
            return Err(NetError::NotFoundError);
        };

        let payload = match handler.try_parse_request(
            preamble,
            &captures,
            if query.is_empty() { None } else { Some(&query) },
            body,
        ) {
            Ok(p) => p,
            Err(e) => {
                handler.restart();
                return Err(e.into());
            }
        };

        let request = StacksHttpRequest::new(preamble.clone(), payload);
        Ok(request)
    }

    /// Try to parse an inbound HTTP request, given its decoded HTTP preamble.
    /// The body will be in the `fd`.
    /// Returns the parsed HTTP request if successful.
    pub fn try_parse_request(
        &mut self,
        preamble: &HttpRequestPreamble,
        body: &[u8],
    ) -> Result<StacksHttpRequest, NetError> {
        let (decoded_path, query) = decode_request_path(&preamble.path_and_query_str)?;
        test_debug!("decoded_path: '{}', query: '{}'", &decoded_path, &query);

        // NOTE: This loop starts out like `find_response_handler()`, but `captures`'s lifetime is
        // bound to `regex` so we can't just return it from `find_response_handler()`.  Thus, it's
        // duplicated here.
        for (verb, regex, request) in self.request_handlers.iter_mut() {
            if &preamble.verb != verb {
                continue;
            }
            let Some(captures) = regex.captures(&decoded_path) else {
                continue;
            };

            let payload = match request.try_parse_request(
                preamble,
                &captures,
                if query.is_empty() { None } else { Some(&query) },
                body,
            ) {
                Ok(p) => p,
                Err(e) => {
                    request.restart();
                    return Err(e.into());
                }
            };

            debug!("Handle StacksHttpRequest"; "verb" => %verb, "peer_addr" => %self.peer_addr, "path" => %decoded_path, "query" => %query);
            let request = StacksHttpRequest::new(preamble.clone(), payload);
            return Ok(request);
        }

        test_debug!("Failed to parse '{}'", &preamble.path_and_query_str);
        Err(NetError::Http(HttpError::Http(
            404,
            "No such file or directory".into(),
        )))
    }

    /// Parse out an HTTP response error message
    pub fn try_parse_error_response(
        preamble: &HttpResponsePreamble,
        body: &[u8],
    ) -> Result<StacksHttpResponse, NetError> {
        if preamble.status_code < 400 || preamble.status_code > 599 {
            return Err(NetError::DeserializeError(
                "Inavlid response: not an error".to_string(),
            ));
        }

        let payload = if preamble.content_type == HttpContentType::Text {
            let mut error_text = String::new();
            let mut ioc = io::Cursor::new(body);
            let mut bound_fd = BoundReader::from_reader(&mut ioc, MAX_MESSAGE_LEN as u64);
            bound_fd
                .read_to_string(&mut error_text)
                .map_err(NetError::ReadError)?;

            HttpResponsePayload::Text(error_text)
        } else if preamble.content_type == HttpContentType::JSON {
            let mut ioc = io::Cursor::new(body);
            let mut bound_fd = BoundReader::from_reader(&mut ioc, MAX_MESSAGE_LEN as u64);
            let json_val = serde_json::from_reader(&mut bound_fd).map_err(|_| {
                NetError::DeserializeError("Failed to decode JSON value".to_string())
            })?;

            HttpResponsePayload::JSON(json_val)
        } else {
            return Err(NetError::DeserializeError(format!(
                "Invalid error response: expected text/plain or application/json, got {:?}",
                &preamble.content_type
            )));
        };

        Ok(StacksHttpResponse::new(preamble.clone(), payload))
    }

    /// Try to parse an inbound HTTP response, given its decoded HTTP preamble, and the HTTP
    /// version and request path that had originally sent.  The body will be read from `fd`.
    pub fn try_parse_response(
        &mut self,
        request_handler_index: usize,
        preamble: &HttpResponsePreamble,
        body: &[u8],
    ) -> Result<StacksHttpResponse, NetError> {
        if preamble.status_code >= 400 {
            return Self::try_parse_error_response(preamble, body);
        }

        let (_, _, parser) = self
            .request_handlers
            .get(request_handler_index)
            .expect("FATAL: tried to use nonexistent response handler");
        let payload = parser.try_parse_response(preamble, body)?;
        let response = StacksHttpResponse::new(preamble.clone(), payload);
        return Ok(response);
    }

    /// Handle an HTTP request by generating an HTTP response.
    /// Returns Ok((preamble, contents)) on success.  Note that this could be an HTTP error
    /// message.
    /// Returns Err(..) on failure to decode or generate the response.
    pub fn try_handle_request(
        &mut self,
        request: StacksHttpRequest,
        node: &mut StacksNodeState,
    ) -> Result<(HttpResponsePreamble, HttpResponseContents), NetError> {
        let (decoded_path, _) = decode_request_path(&request.preamble().path_and_query_str)?;
        let Some(response_handler_index) = request
            .response_handler_index
            .or_else(|| self.find_response_handler(&request.preamble().verb, &decoded_path))
        else {
            // method not found
            return StacksHttpResponse::new_error(
                &request.preamble,
                &HttpNotFound::new(format!(
                    "No such API endpoint '{} {}'",
                    &request.preamble().verb,
                    &decoded_path
                )),
            )
            .try_into_contents();
        };

        let (_, _, request_handler) = self
            .request_handlers
            .get_mut(response_handler_index)
            .expect("FATAL: request points to a nonexistent handler");
        let request_preamble = request.preamble.clone();
        let request_result =
            request_handler.try_handle_request(request.preamble, request.contents, node);
        request_handler.restart();

        let (response_preamble, response_contents) = match request_result {
            Ok((rp, rc)) => (rp, rc),
            Err(NetError::Http(e)) => {
                debug!("RPC handler for {} failed: {:?}", decoded_path, &e);
                return StacksHttpResponse::new_error(&request_preamble, &*e.into_http_error())
                    .try_into_contents();
            }
            Err(e) => {
                warn!("Irrecoverable error when handling request"; "path" => %request_preamble.path_and_query_str, "error" => %e);
                return Err(e);
            }
        };
        Ok((response_preamble, response_contents))
    }

    #[cfg(test)]
    pub fn num_pending(&self) -> usize {
        self.reply.as_ref().map(|_| 1).unwrap_or(0)
    }

    /// Set up the pending response
    /// Called indirectly from ProtocolFamily::read_preamble() when handling an HTTP response
    /// Used for dealing with streaming data
    fn set_pending(&mut self, preamble: &HttpResponsePreamble) {
        self.reply = Some(StacksHttpReplyData {
            request_id: preamble
                .get_request_id()
                .unwrap_or(HTTP_REQUEST_ID_RESERVED),
            stream: StacksHttpRecvStream::new(MAX_MESSAGE_LEN as u64),
        });
    }

    /// Set the preamble. This is only relevant for receiving an HTTP response to a request that we
    /// already sent.  It gets called from ProtocolFamily::read_preamble().
    ///
    /// This method will set up this state machine to consume the message associated with this
    /// premable, if the response is chunked.
    fn set_preamble(&mut self, preamble: &StacksHttpPreamble) -> Result<(), NetError> {
        if let StacksHttpPreamble::Response(ref http_response_preamble) = preamble {
            // we can only receive a response if we're expecting it
            if self.request_handler_index.is_none() && !self.allow_arbitrary_response {
                return Err(NetError::DeserializeError(
                    "Unexpected HTTP response: no active request handler".to_string(),
                ));
            }
            if http_response_preamble.is_chunked() {
                // we can only receive one response at a time
                if self.reply.is_some() {
                    test_debug!("Have pending reply already");
                    return Err(NetError::InProgress);
                }

                self.set_pending(http_response_preamble);
            }
        }
        Ok(())
    }

    /// Clear any pending response state -- i.e. due to a failed request.
    fn reset(&mut self) {
        self.request_handler_index = None;
        self.reply = None;
    }

    /// Used for processing chunk-encoded streams.
    /// Given the preamble and a Read, stream the bytes into a chunk-decoder.  Return the decoded
    /// bytes if we decode an entire stream.  Always return the number of bytes consumed.
    /// Returns Ok((Some(decoded bytes we got, total number of encoded bytes), number of bytes gotten in this call)) if we're done decoding.
    /// Returns Ok((None, number of bytes gotten in this call)) if there's more to decode.
    pub fn consume_data<R: Read>(
        &mut self,
        preamble: &HttpResponsePreamble,
        fd: &mut R,
    ) -> Result<(Option<(Vec<u8>, usize)>, usize), NetError> {
        if !preamble.is_chunked() {
            return Err(NetError::InvalidState);
        }
        if let Some(reply) = self.reply.as_mut() {
            match reply.stream.consume_data(fd).inspect_err(|_e| {
                self.reset();
            })? {
                (Some((byte_vec, bytes_total)), sz) => {
                    // done receiving
                    self.reply = None;
                    Ok((Some((byte_vec, bytes_total)), sz))
                }
                res => Ok(res),
            }
        } else {
            return Err(NetError::InvalidState);
        }
    }

    /// Calculate the search window for \r\n\r\n in the preamble stream.
    ///
    /// As we are streaming the preamble, we're looking for the pattern `\r\n\r\n`.  The last four
    /// bytes of the encoded preamble are always stored in `self.last_four_preamble_bytes`; this
    /// gets updated as the preamble data is streamed in.  So, given these last four bytes, and the
    /// next chunk of data streamed in from the request (in `buf`), determine the 4-byte sequence
    /// to check for `\r\n\r\n`.
    ///
    /// `i` is the offset into the chunk `buf` being searched.  If `i < 4`, then we must check the
    /// last `4 - i` bytes of `self.last_four_preamble_bytes` as well as the first `i` bytes of
    /// `buf`.  Otherwise, we just check `buf[i-4..i]`.
    fn body_start_search_window(&self, i: usize, buf: &[u8]) -> [u8; 4] {
        let window = match i {
            0 => [
                self.last_four_preamble_bytes[0],
                self.last_four_preamble_bytes[1],
                self.last_four_preamble_bytes[2],
                self.last_four_preamble_bytes[3],
            ],
            1 => [
                self.last_four_preamble_bytes[1],
                self.last_four_preamble_bytes[2],
                self.last_four_preamble_bytes[3],
                buf[0],
            ],
            2 => [
                self.last_four_preamble_bytes[2],
                self.last_four_preamble_bytes[3],
                buf[0],
                buf[1],
            ],
            3 => [self.last_four_preamble_bytes[3], buf[0], buf[1], buf[2]],
            _ => [buf[i - 4], buf[i - 3], buf[i - 2], buf[i - 1]],
        };
        window
    }

    /// Get a unique `&str` identifier for each request type
    /// This can only return a finite set of identifiers, which makes it safer to use for Prometheus metrics
    /// For details see https://github.com/stacks-network/stacks-core/issues/4574
    pub fn metrics_identifier(&self, req: &mut StacksHttpRequest) -> &str {
        let Ok((decoded_path, _)) = decode_request_path(req.request_path()) else {
            return "<err-url-decode>";
        };

        let Some(response_handler_index) = req
            .response_handler_index
            .or_else(|| self.find_response_handler(&req.preamble().verb, &decoded_path))
        else {
            return "<err-handler-not-found>";
        };
        req.response_handler_index = Some(response_handler_index);

        let (_, _, request_handler) = self
            .request_handlers
            .get(response_handler_index)
            .expect("FATAL: request points to a nonexistent handler");

        request_handler.metrics_identifier()
    }

    /// Given a fully-formed single HTTP response, parse it (used by clients).
    #[cfg(test)]
    pub fn parse_response(
        verb: &str,
        request_path: &str,
        response_buf: &[u8],
    ) -> Result<StacksHttpMessage, NetError> {
        let mut http = StacksHttp::new(
            "127.0.0.1:20443".parse().unwrap(),
            &ConnectionOptions::default(),
        );
        http.allow_arbitrary_response = true;

        let (preamble, message_offset) = http.read_preamble(response_buf)?;
        let is_chunked = match preamble {
            StacksHttpPreamble::Response(ref resp) => resp.is_chunked(),
            _ => {
                return Err(NetError::DeserializeError(
                    "Invalid HTTP message: did not get a Response preamble".to_string(),
                ));
            }
        };

        let mut message_bytes = &response_buf[message_offset..];

        if is_chunked {
            match http.stream_payload(&preamble, &mut message_bytes)? {
                (Some((message, _)), _) => Ok(message),
                (None, _) => Err(NetError::UnderflowError(
                    "Not enough bytes to form a streamed HTTP response".to_string(),
                )),
            }
        } else {
            let (message, _) = http.read_payload(&preamble, message_bytes)?;
            Ok(message)
        }
    }
}

impl ProtocolFamily for StacksHttp {
    type Preamble = StacksHttpPreamble;
    type Message = StacksHttpMessage;

    /// how big can a preamble get?
    fn preamble_size_hint(&mut self) -> usize {
        HTTP_PREAMBLE_MAX_ENCODED_SIZE as usize
    }

    /// how big is this message?  Might not know if we're dealing with chunked encoding.
    fn payload_len(&mut self, preamble: &StacksHttpPreamble) -> Option<usize> {
        match *preamble {
            StacksHttpPreamble::Request(ref http_request_preamble) => {
                Some(http_request_preamble.get_content_length() as usize)
            }
            StacksHttpPreamble::Response(ref http_response_preamble) => http_response_preamble
                .content_length
                .map(|len| len as usize),
        }
    }

    /// Read the next HTTP preamble (be it a request or a response), and return the preamble and
    /// the number of bytes consumed while reading it.
    fn read_preamble(&mut self, buf: &[u8]) -> Result<(StacksHttpPreamble, usize), NetError> {
        // does this contain end-of-headers marker, including the last four bytes of preamble we
        // saw?
        if self.body_start.is_none() {
            for i in 0..=buf.len() {
                let window = self.body_start_search_window(i, buf);
                if window == [b'\r', b'\n', b'\r', b'\n'] {
                    self.body_start = Some(self.num_preamble_bytes + i);
                }
            }
        }
        if self.body_start.is_none() {
            // haven't found the body yet, so update `last_four_preamble_bytes`
            // and report underflow
            let len = buf.len();
            let last_four_preamble_bytes = self.body_start_search_window(len, buf);
            self.num_preamble_bytes += len;
            self.last_four_preamble_bytes = last_four_preamble_bytes;
            return Err(NetError::UnderflowError(
                "Not enough bytes to form HTTP preamble".into(),
            ));
        }

        let mut cursor = io::Cursor::new(buf);

        let preamble = {
            let mut rd =
                BoundReader::from_reader(&mut cursor, HTTP_PREAMBLE_MAX_ENCODED_SIZE as u64);
            let preamble: StacksHttpPreamble = read_next(&mut rd)?;
            preamble
        };

        let preamble_len = cursor.position() as usize;
        self.set_preamble(&preamble)?;

        Ok((preamble, preamble_len))
    }

    /// Stream a payload of unknown length.  Only gets called if payload_len() returns None.
    ///
    /// Returns Ok((Some((message, num-bytes-consumed)), num-bytes-read)) if we read enough data to
    /// form a message.  `num-bytes-consumed` is the number of bytes required to parse the message,
    /// and `num-bytes-read` is the number of bytes read in this call.
    ///
    /// Returns Ok((None, num-bytes-read)) if we consumed data (i.e. `num-bytes-read` bytes), but
    /// did not yet have enough of the message to parse it.  The caller should try again.
    ///
    /// Returns Error on irrecoverable error.
    fn stream_payload<R: Read>(
        &mut self,
        preamble: &StacksHttpPreamble,
        fd: &mut R,
    ) -> Result<(Option<(StacksHttpMessage, usize)>, usize), NetError> {
        if self.payload_len(preamble).is_some() {
            return Err(NetError::InvalidState);
        }
        match preamble {
            StacksHttpPreamble::Request(_) => {
                // HTTP requests can't be chunk-encoded, so this should never be reached
                return Err(NetError::InvalidState);
            }
            StacksHttpPreamble::Response(ref http_response_preamble) => {
                if !http_response_preamble.is_chunked() {
                    return Err(NetError::InvalidState);
                }

                // sanity check -- if we're receiving a response, then we must have earlier issued
                // a request, or we must be in client mode. Thus, we must already know which
                // response handler to use. Otherwise, someone sent us malforemd data.
                if self.request_handler_index.is_none() && !self.allow_arbitrary_response {
                    self.reset();
                    return Err(NetError::DeserializeError(
                        "Unsolicited HTTP response".to_string(),
                    ));
                }

                // message of unknown length.  Buffer up and maybe we can parse it.
                let (message_bytes_opt, num_read) = self
                    .consume_data(http_response_preamble, fd)
                    .inspect_err(|_e| {
                    self.reset();
                })?;

                match message_bytes_opt {
                    Some((message_bytes, total_bytes_consumed)) => {
                        // can parse!
                        test_debug!(
                            "read http response payload of {} bytes (just buffered {})",
                            message_bytes.len(),
                            num_read,
                        );

                        let parse_res = if self.request_handler_index.is_none()
                            && self.allow_arbitrary_response
                        {
                            let arbitrary_parser = RPCArbitraryResponseHandler {};
                            let response_payload = arbitrary_parser
                                .try_parse_response(http_response_preamble, &message_bytes[..])?;
                            Ok(StacksHttpResponse::new(
                                http_response_preamble.clone(),
                                response_payload,
                            ))
                        } else {
                            // we now know the content-length, so pass it into the parser.
                            let handler_index =
                                self.request_handler_index
                                    .ok_or(NetError::DeserializeError(
                                        "Unknown HTTP response handler".to_string(),
                                    ))?;

                            self.try_parse_response(
                                handler_index,
                                http_response_preamble,
                                &message_bytes[..],
                            )
                        };

                        // done parsing
                        self.reset();
                        match parse_res {
                            Ok(data_response) => Ok((
                                Some((
                                    StacksHttpMessage::Response(data_response),
                                    total_bytes_consumed,
                                )),
                                num_read,
                            )),
                            Err(e) => {
                                info!("Failed to parse HTTP response: {:?}", &e);
                                Err(e)
                            }
                        }
                    }
                    None => {
                        // need more data
                        test_debug!(
                            "did not read http response payload, but buffered {}",
                            num_read
                        );
                        Ok((None, num_read))
                    }
                }
            }
        }
    }

    /// Parse a payload of known length.
    /// Only gets called if payload_len() returns Some(...).
    ///
    /// Return Ok(message, num-bytes-consumed) if we decoded a message.  The message will
    /// have consumed `num-bytes-consumed` bytes.
    ///
    /// Return Err(..) if we failed to decode the message.
    fn read_payload(
        &mut self,
        preamble: &StacksHttpPreamble,
        buf: &[u8],
    ) -> Result<(StacksHttpMessage, usize), NetError> {
        match preamble {
            StacksHttpPreamble::Request(ref http_request_preamble) => {
                // all requests have a known length
                let len = http_request_preamble.get_content_length() as usize;
                if len > buf.len() {
                    return Err(NetError::InvalidState);
                }

                trace!("read http request payload of {} bytes", len);

                match self.try_parse_request(http_request_preamble, &buf[0..len]) {
                    Ok(data_request) => Ok((StacksHttpMessage::Request(data_request), len)),
                    Err(NetError::Http(http_error)) => {
                        // convert into a response
                        let resp = StacksHttpResponse::new_error(
                            http_request_preamble,
                            &*http_error.into_http_error(),
                        );
                        self.reset();
                        return Ok((
                            StacksHttpMessage::Error(
                                http_request_preamble.path_and_query_str.clone(),
                                resp,
                            ),
                            len,
                        ));
                    }
                    Err(e) => {
                        info!("Failed to parse HTTP request: {:?}", &e);
                        self.reset();
                        Err(e)
                    }
                }
            }
            StacksHttpPreamble::Response(ref http_response_preamble) => {
                if http_response_preamble.is_chunked() {
                    return Err(NetError::InvalidState);
                }

                // message of known length
                test_debug!("read http response payload of {} bytes", buf.len(),);

                if self.request_handler_index.is_none() && self.allow_arbitrary_response {
                    let arbitrary_parser = RPCArbitraryResponseHandler {};
                    let response_payload =
                        arbitrary_parser.try_parse_response(http_response_preamble, buf)?;
                    if http_response_preamble.status_code >= 400 {
                        return Ok((
                            StacksHttpMessage::Error(
                                "(client-given)".into(),
                                StacksHttpResponse::new(
                                    http_response_preamble.clone(),
                                    response_payload,
                                ),
                            ),
                            buf.len(),
                        ));
                    } else {
                        return Ok((
                            StacksHttpMessage::Response(StacksHttpResponse::new(
                                http_response_preamble.clone(),
                                response_payload,
                            )),
                            buf.len(),
                        ));
                    }
                }

                // sanity check -- if we're receiving a response, then we must have earlier issued
                // a request. Thus, we must already know which response handler to use.
                // Otherwise, someone sent us malformed data.
                let handler_index = self.request_handler_index.ok_or_else(|| {
                    self.reset();
                    NetError::DeserializeError("Unsolicited HTTP response".to_string())
                })?;

                let res = self.try_parse_response(handler_index, http_response_preamble, buf);
                self.reset();
                res.map(|data_response| (StacksHttpMessage::Response(data_response), buf.len()))
            }
        }
    }

    fn verify_payload_bytes(
        &mut self,
        _key: &StacksPublicKey,
        _preamble: &StacksHttpPreamble,
        _bytes: &[u8],
    ) -> Result<(), NetError> {
        // not defined for HTTP messages, but maybe we could add a signature header at some point
        // in the future if needed.
        Ok(())
    }

    /// Write out a message to `fd`.
    ///
    /// NOTE: If we're sending a StacksHttpMessage::Request(..), then the next preamble and payload
    /// received _must be_ a StacksHttpMessage::Response(..) in response to the request.
    /// If it is not, then that decode will fail.
    fn write_message<W: Write>(
        &mut self,
        fd: &mut W,
        message: &StacksHttpMessage,
    ) -> Result<(), NetError> {
        match *message {
            StacksHttpMessage::Request(ref req) => {
                // the node cannot send more than one request in parallel, unless the client is
                // directing it
                let handler_index = if !self.allow_arbitrary_response {
                    if self.request_handler_index.is_some() {
                        test_debug!("Have pending request already");
                        return Err(NetError::InProgress);
                    }

                    // find the response handler we'll use
                    let (decoded_path, _) =
                        decode_request_path(&req.preamble().path_and_query_str)?;
                    let handler_index = self
                        .find_response_handler(&req.preamble().verb, &decoded_path)
                        .ok_or(NetError::SendError(format!(
                            "No response handler found for `{} {}`",
                            &req.preamble().verb,
                            &decoded_path
                        )))?;
                    Some(handler_index)
                } else {
                    None
                };

                req.send(fd)?;

                // remember this so we'll know how to decode the response.
                // The next preamble and message we'll read _must be_ a response!
                if handler_index.is_some() {
                    self.request_handler_index = handler_index;
                }
                Ok(())
            }
            StacksHttpMessage::Response(ref resp) => resp.send(fd),
            StacksHttpMessage::Error(_, ref resp) => resp.send(fd),
        }
    }
}

impl PeerNetwork {
    /// Send a (non-blocking) HTTP request to a remote peer.
    /// Returns the event ID on success.
    #[cfg_attr(test, mutants::skip)]
    pub fn connect_or_send_http_request(
        &mut self,
        data_url: UrlString,
        addr: SocketAddr,
        request: StacksHttpRequest,
    ) -> Result<usize, NetError> {
        PeerNetwork::with_network_state(self, |ref mut network, ref mut network_state| {
            PeerNetwork::with_http(network, |ref mut network, ref mut http| {
                match http.connect_http(
                    network_state,
                    network,
                    data_url.clone(),
                    addr.clone(),
                    Some(request.clone()),
                ) {
                    Ok(event_id) => Ok(event_id),
                    Err(NetError::AlreadyConnected(event_id, _)) => {
                        if let (Some(ref mut convo), Some(ref mut socket)) =
                            http.get_conversation_and_socket(event_id)
                        {
                            convo.send_request(request)?;
                            HttpPeer::saturate_http_socket(socket, convo)?;
                            Ok(event_id)
                        } else {
                            debug!("HTTP failed to connect to {:?}, {:?}", &data_url, &addr);
                            Err(NetError::PeerNotConnected)
                        }
                    }
                    Err(e) => {
                        return Err(e);
                    }
                }
            })
        })
    }
}

/// Given a raw path, decode it (i.e. if it's url-encoded)
/// Return the (decoded-path, query-string) on success
pub fn decode_request_path(path: &str) -> Result<(String, String), NetError> {
    let local_url = format!("http://local{}", path);
    let url = Url::parse(&local_url).map_err(|_e| {
        NetError::DeserializeError("Http request path could not be parsed".to_string())
    })?;

    let decoded_path = percent_decode_str(url.path()).decode_utf8().map_err(|_e| {
        NetError::DeserializeError("Http request path could not be parsed as UTF-8".to_string())
    })?;

    let query_str = url.query();
    Ok((
        decoded_path.to_string(),
        query_str.unwrap_or("").to_string(),
    ))
}

/// Convert a NetError into an io::Error if appropriate.
fn handle_net_error(e: NetError, msg: &str) -> io::Error {
    match e {
        NetError::ReadError(ioe) | NetError::WriteError(ioe) => ioe,
        NetError::RecvTimeout => io::Error::new(io::ErrorKind::WouldBlock, "recv timeout"),
        _ => io::Error::new(io::ErrorKind::Other, format!("{}: {:?}", &e, msg).as_str()),
    }
}

/// Send an HTTP request to the given host:port.  Returns the decoded response.
/// Internally, this creates a socket, connects it, sends the HTTP request, and decodes the HTTP
/// response.  It is a blocking operation.
///
/// If the request encounters a network error, then return an error.  Don't retry.
/// If the request times out after `timeout`, then return an error.
pub fn send_http_request(
    host: &str,
    port: u16,
    request: StacksHttpRequest,
    timeout: Duration,
) -> Result<StacksHttpResponse, io::Error> {
    // Find the host:port that works.
    // This is sometimes necessary because `localhost` can resolve to both its ipv4 and ipv6
    // addresses, but usually, Stacks services like event observers are only bound to ipv4
    // addresses.  So, be sure to use an address that will lead to a socket connection!
    let mut stream_and_addr = None;
    let mut last_err = None;
    for addr in format!("{host}:{port}").to_socket_addrs()? {
        debug!("send_request: connect to {}", &addr);
        match TcpStream::connect_timeout(&addr, timeout) {
            Ok(sock) => {
                stream_and_addr = Some((sock, addr));
                break;
            }
            Err(e) => {
                last_err = Some(e);
            }
        }
    }

    let Some((mut stream, addr)) = stream_and_addr else {
        return Err(last_err.unwrap_or(io::Error::new(
            io::ErrorKind::Other,
            "Unable to connect to {host}:{port}",
        )));
    };

    stream.set_read_timeout(Some(timeout))?;
    stream.set_write_timeout(Some(timeout))?;
    stream.set_nodelay(true)?;

    let start = Instant::now();

    debug!("send_request: Sending request"; "request" => %request.request_path());

    // Some explanation of what's going on here is in order.
    //
    // The networking stack in Stacks is designed to operate on non-blocking sockets, and
    // furthermore, it operates in a way that the call site in which a network request is issued can
    // be in a wholly separate stack (or thread) from the connection.  While this is absolutely necessary
    // within the Stacks node, using it to issue a single blocking request imposes a lot of
    // overhead.
    //
    // First, we will create the network connection and give it a ProtocolFamily implementation
    // (StacksHttp), which gets used by the connection to encode and deocde messages.
    //
    // Second, we'll create a _handle_ to the network connection into which we will write requests
    // and read responses.  The connection itself is an opaque black box that, internally,
    // implements a state machine around the ProtocolFamily implementation to incrementally read
    // ProtocolFamily messages from a Read, and write them to a Write.  The Read + Write is
    // (usually) a non-blocking socket; the network connection deals with EWOULDBLOCK internally,
    // as well as underfull socket buffers.
    //
    // Third, we need to _drive_ data to the socket.  We have to repeatedly (1) flush the network
    // handle (which contains the buffered bytes from the message to be fed into the socket), and
    // (2) drive bytes from the handle into the socket iself via the network connection.  This is a
    // two-step process mainly because the handle is expected to live in a separate stack (or even
    // a separate thread).
    //
    // Fourth, we need to _drive_ data from the socket.  We have to repeatedly (1) pull data from
    // the socket into the network connection, and (2) drive parsed messages from the connection to
    // the handle.  Then, the call site that owns the handle simply polls the handle for new
    // messages.  Once we have received a message, we can proceed to handle it.
    //
    // Finally, we deal with the kind of HTTP message we got. If it's an error response, we convert
    // it into an error.  If it's a request (i.e. not a response), we also return an error.  We
    // only return the message if it was a well-formed non-error HTTP response.

    // Step 1-2: set up the connection and request handle
    // NOTE: we don't need anything special for connection options, so just use the default
    let conn_opts = ConnectionOptions::default();
    let http = StacksHttp::new_client(addr, &conn_opts);
    let mut connection = NetworkConnection::new(http, &conn_opts, None);
    let mut request_handle = connection
        .make_request_handle(0, get_epoch_time_secs() + timeout.as_secs(), 0)
        .map_err(|e| {
            io::Error::new(
                io::ErrorKind::Other,
                format!("Failed to create request handle: {:?}", &e).as_str(),
            )
        })?;

    // Step 3: load up the request with the message we're gonna send, and iteratively dump its
    // bytes from the handle into the socket (the connection does internal buffering and
    // bookkeeping to deal with the cases where we fail to fill the socket buffer, or we can't send
    // anymore because the socket buffer is currently full).
    request
        .send(&mut request_handle)
        .map_err(|e| handle_net_error(e, "Failed to serialize request body"))?;

    debug!("send_request(sending data)");
    loop {
        let flushed = request_handle
            .try_flush()
            .map_err(|e| handle_net_error(e, "Failed to flush request body"))?;

        // send it out
        let num_sent = connection
            .send_data(&mut stream)
            .map_err(|e| handle_net_error(e, "Failed to send socket data"))?;

        debug!(
            "send_request(sending data): flushed = {}, num_sent = {}",
            flushed, num_sent
        );
        if flushed && num_sent == 0 {
            break;
        }

        if Instant::now().saturating_duration_since(start) > timeout {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "Timed out while receiving request",
            ));
        }
    }

    // Step 4: pull bytes from the socket back into the handle, and see if the connection decoded
    // and dispatched any new messages to the request handle.  If so, then extract the message and
    // check that it's a well-formed HTTP response.
    debug!("send_request(receiving data)");
    let response = loop {
        // get back the reply
        debug!("send_request(receiving data): try to receive data");
        match connection.recv_data(&mut stream) {
            Ok(nr) => {
                debug!("send_request(receiving data): received {} bytes", nr);
            }
            Err(e) => {
                return Err(handle_net_error(e, "Failed to receive socket data"));
            }
        }

        // fullfill the request -- send it to its corresponding handle
        debug!("send_request(receiving data): drain inbox");
        connection.drain_inbox();

        // see if we got a message that was fulfilled in our handle
        debug!("send_request(receiving data): try receive response");
        let rh = match request_handle.try_recv() {
            Ok(resp) => {
                break resp;
            }
            Err(Ok(handle)) => handle,
            Err(Err(e)) => {
                return Err(handle_net_error(
                    e,
                    "Failed to receive message after socket has been drained",
                ));
            }
        };
        request_handle = rh;

        if Instant::now().saturating_duration_since(start) > timeout {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "Timed out while receiving request",
            ));
        }
    };

    // Step 5: decode the HTTP message and return it if it's not an error.
    let response_data = match response {
        StacksHttpMessage::Response(response_data) => response_data,
        StacksHttpMessage::Error(_path, response) => {
            let verb = &request.preamble().verb;
            let path = &request.preamble().path_and_query_str;
            let resp_status_code = response.preamble().status_code;
            let resp_body = response.body();
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!(
                    "HTTP '{verb} {path}' did not succeed ({resp_status_code} != 200). Response body = {resp_body:?}"
                ),
            ));
        }
        _ => {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                "Did not receive an HTTP response",
            ));
        }
    };

    Ok(response_data)
}
