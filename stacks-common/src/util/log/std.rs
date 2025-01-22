// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
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

use std::io::Write;
use std::sync::Mutex;
use std::time::{Duration, SystemTime};
use std::{env, io, thread};

use chrono::prelude::*;
use lazy_static::lazy_static;
use slog::{BorrowedKV, Drain, FnValue, Level, Logger, OwnedKVList, Record, KV};
use slog_term::{CountingWriter, Decorator, RecordDecorator, Serializer};

lazy_static! {
    pub static ref LOGGER: Logger = make_logger();
    pub static ref STACKS_LOG_FORMAT_TIME: Option<String> = env::var("STACKS_LOG_FORMAT_TIME").ok();
}
struct TermFormat<D: Decorator> {
    decorator: D,
    pretty_print: bool,
    debug: bool,
    isatty: bool,
}

fn print_msg_header(mut rd: &mut dyn RecordDecorator, record: &Record) -> io::Result<bool> {
    rd.start_level()?;
    write!(rd, "{}", record.level().as_short_str())?;
    rd.start_whitespace()?;
    write!(rd, " ")?;

    rd.start_timestamp()?;
    let system_time = SystemTime::now();
    match &*STACKS_LOG_FORMAT_TIME {
        None => {
            let elapsed = system_time
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap_or(Duration::from_secs(0));
            write!(
                rd,
                "[{:5}.{:06}]",
                elapsed.as_secs(),
                elapsed.subsec_micros()
            )?;
        }
        Some(ref format) => {
            let datetime: DateTime<Local> = system_time.into();
            write!(rd, "[{}]", datetime.format(format))?;
        }
    }
    write!(rd, " ")?;
    write!(rd, "[{}:{}]", record.file(), record.line())?;
    write!(rd, " ")?;
    match thread::current().name() {
        None => write!(rd, "[{:?}]", thread::current().id())?,
        Some(name) => write!(rd, "[{}]", name)?,
    }

    rd.start_whitespace()?;
    write!(rd, " ")?;

    rd.start_msg()?;
    let mut count_rd = CountingWriter::new(&mut rd);
    write!(count_rd, "{}", record.msg())?;
    Ok(count_rd.count() != 0)
}

fn pretty_print_msg_header(
    rd: &mut dyn RecordDecorator,
    record: &Record,
    debug: bool,
    isatty: bool,
) -> io::Result<bool> {
    rd.start_timestamp()?;
    let now: DateTime<Utc> = Utc::now();
    write!(
        rd,
        "{}{}",
        color_if_tty("\x1b[0;90m", isatty),
        now.format("%b %e %T%.6f")
    )?;
    rd.start_whitespace()?;
    write!(rd, " ")?;

    rd.start_level()?;

    match record.level() {
        Level::Critical | Level::Error => write!(
            rd,
            "{}{}{}",
            color_if_tty("\x1b[0;91m", isatty),
            record.level().as_short_str(),
            color_if_tty("\x1b[0m", isatty)
        ),
        Level::Warning => write!(
            rd,
            "{}{}{}",
            color_if_tty("\x1b[0;33m", isatty),
            record.level().as_short_str(),
            color_if_tty("\x1b[0m", isatty)
        ),
        Level::Info => write!(
            rd,
            "{}{}{}",
            color_if_tty("\x1b[0;94m", isatty),
            record.level().as_short_str(),
            color_if_tty("\x1b[0m", isatty)
        ),
        _ => write!(rd, "{}", record.level().as_short_str()),
    }?;

    rd.start_whitespace()?;
    write!(rd, " ")?;

    rd.start_msg()?;
    write!(rd, "{}", record.msg())?;

    if debug {
        write!(rd, " ")?;
        write!(
            rd,
            "{}({:?}, {}:{}){}",
            color_if_tty("\x1b[0;90m", isatty),
            thread::current().id(),
            record.file(),
            record.line(),
            color_if_tty("\x1b[0m", isatty)
        )?;
    }

    Ok(true)
}

impl<D: Decorator> Drain for TermFormat<D> {
    type Ok = ();
    type Err = io::Error;

    fn log(&self, record: &Record, values: &OwnedKVList) -> Result<Self::Ok, Self::Err> {
        self.format_full(record, values)
    }
}

impl<D: Decorator> TermFormat<D> {
    pub fn new(decorator: D, pretty_print: bool, debug: bool, isatty: bool) -> TermFormat<D> {
        TermFormat {
            decorator,
            pretty_print,
            debug,
            isatty,
        }
    }

    fn format_full(&self, record: &Record, values: &OwnedKVList) -> io::Result<()> {
        self.decorator.with_record(record, values, |decorator| {
            let comma_needed = if self.pretty_print {
                pretty_print_msg_header(decorator, record, self.debug, self.isatty)
            } else {
                print_msg_header(decorator, record)
            }?;
            {
                let mut serializer = Serializer::new(decorator, comma_needed, true);

                record.kv().serialize(record, &mut serializer)?;

                values.serialize(record, &mut serializer)?;

                serializer.finish()?;
            }

            decorator.start_whitespace()?;
            writeln!(decorator)?;

            decorator.flush()?;

            Ok(())
        })
    }
}

#[cfg(feature = "slog_json")]
fn make_json_logger() -> Logger {
    let def_keys = o!("file" => FnValue(move |info| {
                          info.file()
                      }),
                      "line" => FnValue(move |info| {
                          info.line()
                      }),
                      "thread" => FnValue(move |_| {
                          match thread::current().name() {
                              None => format!("{:?}", thread::current().id()),
                              Some(name) => name.to_string(),
                          }
                      }),
    );

    let drain = Mutex::new(slog_json::Json::default(std::io::stderr()));
    let filtered_drain = slog::LevelFilter::new(drain, get_loglevel()).ignore_res();
    slog::Logger::root(filtered_drain, def_keys)
}

#[cfg(not(feature = "slog_json"))]
fn make_json_logger() -> Logger {
    panic!("Tried to construct JSON logger, but stacks-blockchain built without slog_json feature enabled.")
}

fn make_logger() -> Logger {
    if env::var("STACKS_LOG_JSON") == Ok("1".into()) {
        make_json_logger()
    } else {
        let debug = env::var("STACKS_LOG_DEBUG") == Ok("1".into());
        let pretty_print = env::var("STACKS_LOG_PP") == Ok("1".into());
        let decorator = get_decorator();
        let atty = isatty(Stream::Stderr);
        let drain = TermFormat::new(decorator, pretty_print, debug, atty);
        Logger::root(drain.ignore_res(), o!())
    }
}

#[cfg(any(test, feature = "testing"))]
fn get_decorator() -> slog_term::PlainSyncDecorator<slog_term::TestStdoutWriter> {
    slog_term::PlainSyncDecorator::new(slog_term::TestStdoutWriter)
}

#[cfg(not(any(test, feature = "testing")))]
fn get_decorator() -> slog_term::PlainSyncDecorator<std::io::Stderr> {
    slog_term::PlainSyncDecorator::new(std::io::stderr())
}

fn inner_get_loglevel() -> slog::Level {
    if env::var("STACKS_LOG_TRACE") == Ok("1".into()) {
        slog::Level::Trace
    } else if env::var("STACKS_LOG_DEBUG") == Ok("1".into())
        || env::var("BLOCKSTACK_DEBUG") == Ok("1".into())
    {
        slog::Level::Debug
    } else if env::var("STACKS_LOG_CRITONLY") == Ok("1".into()) {
        slog::Level::Critical
    } else {
        slog::Level::Info
    }
}

lazy_static! {
    static ref LOGLEVEL: slog::Level = inner_get_loglevel();
}

pub fn get_loglevel() -> slog::Level {
    *LOGLEVEL
}

#[macro_export]
macro_rules! trace {
    ($($arg:tt)*) => ({
        let cur_level = $crate::util::log::get_loglevel();
        if slog::Level::Trace.is_at_least(cur_level) {
            slog_trace!($crate::util::log::LOGGER, $($arg)*)
        }
    })
}

#[macro_export]
macro_rules! error {
    ($($arg:tt)*) => ({
        let cur_level = $crate::util::log::get_loglevel();
        if slog::Level::Error.is_at_least(cur_level) {
            slog_error!($crate::util::log::LOGGER, $($arg)*)
        }
    })
}

#[macro_export]
macro_rules! warn {
    ($($arg:tt)*) => ({
        let cur_level = $crate::util::log::get_loglevel();
        if slog::Level::Warning.is_at_least(cur_level) {
            slog_warn!($crate::util::log::LOGGER, $($arg)*)
        }
    })
}

#[macro_export]
macro_rules! info {
    ($($arg:tt)*) => ({
        let cur_level = $crate::util::log::get_loglevel();
        if slog::Level::Info.is_at_least(cur_level) {
            slog_info!($crate::util::log::LOGGER, $($arg)*)
        }
    })
}

#[macro_export]
macro_rules! debug {
    ($($arg:tt)*) => ({
        let cur_level = $crate::util::log::get_loglevel();
        if slog::Level::Debug.is_at_least(cur_level) {
            slog_debug!($crate::util::log::LOGGER, $($arg)*)
        }
    })
}

#[macro_export]
macro_rules! fatal {
    ($($arg:tt)*) => ({
        let cur_level = $crate::util::log::get_loglevel();
        if slog::Level::Critical.is_at_least(cur_level) {
            slog_crit!($crate::util::log::LOGGER, $($arg)*)
        }
    })
}

fn color_if_tty(color: &str, isatty: bool) -> &str {
    if isatty {
        color
    } else {
        ""
    }
}

enum Stream {
    Stdout,
    Stderr,
}

#[cfg(unix)]
fn isatty(stream: Stream) -> bool {
    let fd = match stream {
        Stream::Stdout => libc::STDOUT_FILENO,
        Stream::Stderr => libc::STDERR_FILENO,
    };
    unsafe { libc::isatty(fd) != 0 }
}

#[cfg(not(unix))]
fn isatty(stream: Stream) -> bool {
    false
}
