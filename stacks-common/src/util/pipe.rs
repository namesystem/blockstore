/*
 copyright: (c) 2013-2020 by Blockstack PBC, a public benefit corporation.

 This file is part of Blockstack.

 Blockstack is free software. You may redistribute or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License or
 (at your option) any later version.

 Blockstack is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY, including without the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with Blockstack. If not, see <http://www.gnu.org/licenses/>.
*/

use std::io;
use std::io::{Read, Write};
use std::sync::mpsc::{sync_channel, Receiver, SyncSender, TryRecvError, TrySendError};

/// Inter-thread pipe for streaming messages, built on channels.
/// Used mainly in conjunction with networking.
///
/// * The read endpoint lives inside the connection and will consume data from another thread
///   to be sent out on the network.
/// * The write endpoint gets fed into calls to `consensus_serialize()` to be sent out on the
///   network.
#[derive(Debug)]
pub struct PipeRead {
    input: Receiver<Vec<u8>>,
    buf: Vec<u8>,
    i: usize,
    block: bool,
}

#[derive(Debug)]
pub struct PipeWrite {
    output: SyncSender<Vec<u8>>,
    buf: Option<Vec<u8>>,
}

pub struct Pipe {}

#[allow(clippy::new_ret_no_self)]
impl Pipe {
    pub fn new() -> (PipeRead, PipeWrite) {
        let (send, recv) = sync_channel(1);
        (PipeRead::new(recv), PipeWrite::new(send))
    }
}

impl PipeRead {
    fn new(input: Receiver<Vec<u8>>) -> PipeRead {
        PipeRead {
            input,
            buf: vec![],
            i: 0,
            block: true,
        }
    }

    pub fn set_nonblocking(&mut self, flag: bool) {
        self.block = !flag;
    }

    fn drain_buf(&mut self, buf: &mut [u8]) -> usize {
        if self.i < self.buf.len() {
            // have buffered data from the last read
            let buf_available = &self.buf[self.i..];
            let to_copy = if buf_available.len() < buf.len() {
                buf_available.len()
            } else {
                buf.len()
            };

            if to_copy > 0 {
                trace!(
                    "Pipe read {} bytes from buffer [{}...]",
                    to_copy,
                    buf_available[0]
                );
            }
            buf[..to_copy].copy_from_slice(&buf_available[..to_copy]);
            self.i += to_copy;

            if self.i >= self.buf.len() {
                trace!("Pipe read buffer drained from {} bytes", self.i);

                // drained!
                self.buf.clear();
                self.i = 0;
            }

            to_copy
        } else {
            0
        }
    }

    fn fill_buf(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        assert_eq!(self.buf.len(), 0);
        assert_eq!(self.i, 0);

        let mut copied = 0;
        let mut disconnected = false;
        let mut blocked = false;
        while copied < buf.len() && !disconnected && !blocked {
            let next_bytes = match self.input.try_recv() {
                Ok(bytes) => {
                    trace!("Pipe received {} bytes", bytes.len());
                    bytes
                }
                Err(tre) => match tre {
                    TryRecvError::Empty => {
                        // no data yet
                        if self.block {
                            match self.input.recv() {
                                Ok(bytes) => bytes,
                                Err(_e) => {
                                    // dead
                                    trace!("Pipe read disconnect on blocking read ({})", _e);
                                    disconnected = true;
                                    vec![]
                                }
                            }
                        } else {
                            trace!("Pipe read {} bytes before blocking", copied);
                            blocked = true;
                            vec![]
                        }
                    }
                    TryRecvError::Disconnected => {
                        // dead
                        trace!("Pipe read disconnect");
                        disconnected = true;
                        vec![]
                    }
                },
            };

            let remaining = buf[copied..].len();
            let to_copy = if next_bytes.len() < remaining {
                next_bytes.len()
            } else {
                remaining
            };

            trace!(
                "Pipe read copied {} bytes from channel ({} total)",
                to_copy,
                copied
            );
            buf[copied..(copied + to_copy)].copy_from_slice(&next_bytes[0..to_copy]);
            copied += to_copy;

            // buffer remainder
            if copied == buf.len() && to_copy < next_bytes.len() {
                trace!(
                    "Pipe read buffered {} bytes [{}...]",
                    &next_bytes[to_copy..].len(),
                    next_bytes[to_copy]
                );
                self.buf.extend_from_slice(&next_bytes[to_copy..]);
            }
        }

        if disconnected && copied == 0 {
            // out of data, and will never get more
            return Err(io::Error::from(io::ErrorKind::BrokenPipe));
        }

        if blocked && copied == 0 {
            return Err(io::Error::from(io::ErrorKind::WouldBlock));
        }

        Ok(copied)
    }
}

impl PipeWrite {
    fn new(output: SyncSender<Vec<u8>>) -> PipeWrite {
        PipeWrite { output, buf: None }
    }

    fn write_or_buffer(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }

        // add buf to our internal buffer...
        if self.buf.is_none() {
            let data = buf.to_vec();
            self.buf = Some(data);
        } else {
            let mut tmp = self.buf.take().unwrap(); // safe due to check above
            tmp.extend_from_slice(buf);
            self.buf = Some(tmp);
        }

        // will be Some() either way
        let data = self.buf.take().unwrap();
        let _len = data.len();

        // ...and try to send the whole thing over
        match self.output.try_send(data) {
            Ok(_) => {
                trace!("Pipe wrote {} bytes", _len);
            }
            Err(TrySendError::Full(data)) => {
                trace!("Pipe write buffered {} bytes", data.len());
                self.buf = Some(data);
            }
            Err(TrySendError::Disconnected(_)) => {
                // will never succeed
                return Err(io::Error::from(io::ErrorKind::BrokenPipe));
            }
        }

        // either way we consumed it
        Ok(buf.len())
    }

    /// How many bytes are pending?
    pub fn pending(&self) -> usize {
        self.buf.as_ref().map(|b| b.len()).unwrap_or(0)
    }

    /// Try and flush all data to the reader.
    /// Return True if we succeeded; False if not.
    pub fn try_flush(&mut self) -> io::Result<bool> {
        let data = self.buf.take();
        if let Some(bytes) = data {
            match self.output.try_send(bytes) {
                Err(TrySendError::Full(ret_bytes)) => {
                    // try again
                    self.buf = Some(ret_bytes);
                    Ok(false)
                }
                Err(TrySendError::Disconnected(_)) => {
                    // broken
                    Err(io::Error::from(io::ErrorKind::BrokenPipe))
                }
                Ok(_) => {
                    // sent!
                    Ok(true)
                }
            }
        } else {
            // done!
            Ok(true)
        }
    }
}

impl Read for PipeRead {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let copied = self.drain_buf(buf);
        if copied == buf.len() {
            trace!(
                "Read {} bytes total from buffer (pipe channel not used)",
                copied
            );
            return Ok(copied);
        }

        let filled = match self.fill_buf(&mut buf[copied..]) {
            Ok(cnt) => cnt,
            Err(e) => match e.kind() {
                io::ErrorKind::BrokenPipe | io::ErrorKind::WouldBlock => {
                    if copied > 0 {
                        // if we get EPIPE or EWOULDBLOCK when getting data from the writer, but we hit the
                        // buffer, then this isn't a failure.
                        0
                    } else {
                        trace!("Error reading from pipe: {:?}", &e);
                        return Err(e);
                    }
                }
                _ => {
                    trace!("Error reading from pipe: {:?}", &e);
                    return Err(e);
                }
            },
        };

        trace!(
            "Read {} bytes total from pipe channel and buffer",
            copied + filled
        );
        Ok(copied + filled)
    }
}

impl Write for PipeWrite {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_or_buffer(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        if let Some(bytes) = self.buf.take() {
            let _len = bytes.len();
            self.output
                .send(bytes)
                .map_err(|_e| io::Error::from(io::ErrorKind::BrokenPipe))?;

            trace!("Pipe wrote {} bytes on flush", _len);
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::io::prelude::*;
    use std::io::{Read, Write};
    use std::{io, thread};

    use rand;
    use rand::RngCore;

    use super::*;
    use crate::util::*;

    #[test]
    fn test_connection_pipe_oneshot() {
        let tests = vec![
            // .0: the list of vecs to send to the writer
            // .1: the number of bytes to read each time
            // .2: the expected Result<num-bytes-total, error-encountered>
            (vec![0, 1, 2], vec![3], vec![Ok(3)]),
            (vec![0, 1, 2], vec![1, 2], vec![Ok(1), Ok(2)]),
            (vec![0, 1, 2], vec![1, 1, 1], vec![Ok(1), Ok(1), Ok(1)]),
            (vec![0, 1, 2], vec![0, 3], vec![Ok(0), Ok(3)]),
            (vec![0, 1, 2], vec![4], vec![Ok(3)]),
            (
                vec![0, 1, 2],
                vec![4, 1],
                vec![Ok(3), Err(io::Error::from(io::ErrorKind::WouldBlock))],
            ),
        ];

        for (send_bytes, recv_list, outputs) in tests.iter() {
            test_debug!(
                "send {:?}, recv {:?}, expect {:?}",
                send_bytes,
                recv_list,
                outputs
            );

            assert_eq!(recv_list.len(), outputs.len());

            let (mut pipe_read, mut pipe_write) = Pipe::new();
            let mut recv_buf = vec![];
            let expected_recv_buf = send_bytes.clone();

            pipe_read.set_nonblocking(true);
            let _ = pipe_write.write(&send_bytes[..]).unwrap();

            for i in 0..recv_list.len() {
                let mut buf = vec![0u8; recv_list[i]];
                match pipe_read.read(&mut buf) {
                    Ok(num_bytes) => {
                        assert!(
                            outputs[i].is_ok(),
                            "Expected {:?}, got Ok({})",
                            &outputs[i],
                            num_bytes
                        );

                        let num_bytes_expected = outputs[i].as_ref().ok().unwrap();
                        assert_eq!(
                            num_bytes, *num_bytes_expected,
                            "Expected {}, got {}",
                            num_bytes, num_bytes_expected
                        );

                        recv_buf.extend_from_slice(&buf[0..num_bytes]);
                    }
                    Err(e) => {
                        assert!(
                            outputs[i].is_err(),
                            "Expected {:?}, got Err({:?})",
                            &outputs[i],
                            &e
                        );

                        let expected_output_err = outputs[i].as_ref().err().unwrap();
                        assert_eq!(
                            expected_output_err.kind(),
                            e.kind(),
                            "I/O error mismatch: expected {:?}, got {:?}",
                            e.kind(),
                            expected_output_err.kind()
                        );
                    }
                }
            }

            assert_eq!(recv_buf, expected_recv_buf);
        }
    }

    #[test]
    fn test_connection_pipe_producer_consumer() {
        let mut buf = vec![0; 1048576];

        let mut rng = rand::thread_rng();
        rng.fill_bytes(&mut buf);

        let buf_compare = buf.clone(); // for use in the consumer

        let (mut pipe_read, mut pipe_write) = Pipe::new();
        pipe_read.set_nonblocking(false);

        let producer = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut i = 0;
            let mut broken_pipe = false;
            while i < buf.len() && !broken_pipe {
                let mut span = (rng.next_u32() % 4096) as usize;
                if i + span > buf.len() {
                    span = buf.len() - i;
                }

                let nw = match pipe_write.write(&buf[i..(i + span)]) {
                    Ok(sz) => sz,
                    Err(e) => match e.kind() {
                        io::ErrorKind::BrokenPipe => {
                            broken_pipe = true;
                            0
                        }
                        _ => {
                            assert!(false, "unwrapped err: {:?}", &e);
                            unreachable!();
                        }
                    },
                };

                i += span;
            }
            let _ = pipe_write.flush();

            if broken_pipe {
                assert_eq!(i, buf.len());
            }

            test_debug!("producer exit; wrote {} bytes", i);
        });

        let consumer = thread::spawn(move || {
            let mut rng = rand::thread_rng();
            let mut input = vec![];
            let mut broken_pipe = false;
            while input.len() < buf_compare.len() && !broken_pipe {
                let span = (rng.next_u32() % 4096) as usize;
                let mut next_bytes = vec![0u8; span];

                let nr = match pipe_read.read(&mut next_bytes[..]) {
                    Ok(sz) => sz,
                    Err(e) => match e.kind() {
                        io::ErrorKind::BrokenPipe => {
                            test_debug!("Read pipe broke");
                            broken_pipe = true;
                            0
                        }
                        _ => {
                            assert!(false, "unwrapped err: {:?}", &e);
                            unreachable!();
                        }
                    },
                };

                input.extend_from_slice(&next_bytes[0..nr]);

                test_debug!("Read buffer added {} bytes (now {})", nr, input.len());
                assert!(
                    nr == span || input.len() == buf_compare.len(),
                    "nr = {}, span = {}, input.len() = {}, buf_compare.len() = {}",
                    nr,
                    span,
                    input.len(),
                    buf_compare.len()
                );
            }
            test_debug!("consumer exit; read {} bytes", input.len());

            if broken_pipe {
                assert_eq!(input.len(), buf_compare.len());
            }

            assert_eq!(input, buf_compare.to_vec());
        });

        producer.join().unwrap();
        consumer.join().unwrap();
    }

    #[test]
    fn test_pipe_nonblocking_try_flush() {
        let mut rng = rand::thread_rng();
        let mut input = vec![];
        for i in 0..100 {
            let span = ((rng.next_u32() % 4096) + 1) as usize;
            let mut next_bytes = vec![0u8; span];
            rng.fill_bytes(&mut next_bytes);
            input.push(next_bytes);
        }

        let (mut pipe_read, mut pipe_write) = Pipe::new();
        pipe_read.set_nonblocking(true);

        // test write/read over and over
        for segment in input.iter() {
            let mut bytes = vec![0u8; segment.len()];

            // read should fail with EWOULDBLOCK
            let res = pipe_read.read(&mut bytes).unwrap_err();
            assert_eq!(res.kind(), io::ErrorKind::WouldBlock);

            let _ = pipe_write.write(segment).unwrap();

            // should should succeed since the data is in the receiver's inbox
            let res = pipe_write.try_flush().unwrap();
            assert!(res);

            // read all data (should work now)
            let nr = pipe_read.read(&mut bytes).unwrap();
            assert_eq!(nr, segment.len());
            assert_eq!(*segment, bytes);

            // subsequent read fails with EWOULDBLOCK
            let mut next_bytes = vec![0u8];
            let res = pipe_read.read(&mut next_bytes).unwrap_err();
            assert_eq!(res.kind(), io::ErrorKind::WouldBlock);

            // flush should have succeeded
            let res = pipe_write.try_flush().unwrap();
            assert!(res);
        }

        // subsequent read fails with EWOULDBLOCK
        let mut next_bytes = vec![0u8];
        let res = pipe_read.read(&mut next_bytes).unwrap_err();
        assert_eq!(res.kind(), io::ErrorKind::WouldBlock);

        // once the write end is dropped, then this data is still consumable but we get broken-pipe
        // once it's all been read.
        let _ = pipe_write.write(&[1u8, 1u8]).unwrap();
        drop(pipe_write);

        let mut next_bytes = vec![0u8];
        let res = pipe_read.read(&mut next_bytes).unwrap();
        assert_eq!(res, 1);

        let mut next_bytes = vec![0u8];
        let res = pipe_read.read(&mut next_bytes).unwrap();
        assert_eq!(res, 1);

        let mut next_bytes = vec![0u8];
        let res = pipe_read.read(&mut next_bytes).unwrap_err();
        assert_eq!(res.kind(), io::ErrorKind::BrokenPipe);
    }

    #[test]
    fn test_pipe_nonblocking_try_flush_multiple_write() {
        let mut rng = rand::thread_rng();
        let mut input = vec![];
        for i in 0..100 {
            let span = ((rng.next_u32() % 4096) + 1) as usize;
            let mut next_bytes = vec![0u8; span];
            rng.fill_bytes(&mut next_bytes);
            input.push(next_bytes);
        }

        let (mut pipe_read, mut pipe_write) = Pipe::new();
        pipe_read.set_nonblocking(true);

        // test write/read over and over, but issue multiple writes.
        // The first write should be flushed, but until a read happens,
        // the subsequent writes should not flush.
        for segment in input.iter() {
            let mut bytes = vec![0u8; segment.len()];

            // read should fail with EWOULDBLOCK
            let res = pipe_read.read(&mut bytes).unwrap_err();
            assert_eq!(res.kind(), io::ErrorKind::WouldBlock);

            // write each _byte_
            for (i, byte) in segment.iter().enumerate() {
                let _ = pipe_write.write(&[*byte]).unwrap();
                let res = pipe_write.try_flush().unwrap();

                // first write flushes; subsequent ones don't
                if i == 0 {
                    assert!(res);
                } else {
                    assert!(!res);
                }
            }

            // first read gets back 1 byte
            let nr = pipe_read.read(&mut bytes).unwrap();
            assert_eq!(nr, 1);
            assert_eq!(bytes[0], segment[0]);

            // try_flush puts all data into the reader's inbox,
            // and drains the write buffer.
            let res = pipe_write.try_flush().unwrap();
            assert!(res);

            // next read gets back the remaining data
            let nr = pipe_read.read(&mut bytes[1..]).unwrap();
            assert_eq!(nr, segment.len() - 1);
            assert_eq!(*segment, bytes);

            // subsequent read fails with EWOULDBLOCK
            let mut next_bytes = vec![0u8];
            let res = pipe_read.read(&mut next_bytes).unwrap_err();
            assert_eq!(res.kind(), io::ErrorKind::WouldBlock);

            // flush should have succeeded
            let res = pipe_write.try_flush().unwrap();
            assert!(res);
        }
    }
}
