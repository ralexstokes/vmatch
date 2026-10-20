//! Fixed-size little-endian binary encoding for commands and events.
//!
//! Command frame (24 bytes):
//! ```text
//!  0      kind      1 = New, 2 = Cancel, 3 = Replace
//!  1      side      0 = Buy, 1 = Sell            (Replace: post_only 0/1)
//!  2      ord_type  0 = Limit, 1 = Market
//!  3      tif       0 = GTC, 1 = IOC, 2 = FOK, 3 = PostOnly
//!  4..8   price     u32 tick index
//!  8..16  qty       u64
//! 16..24  id        u64 (Cancel / Replace)
//! ```
//!
//! Event record (32 bytes):
//! ```text
//!  0      kind      1 Accepted, 2 Fill, 3 Rested, 4 Expired, 5 Cancelled, 6 Reduced, 7 Rejected
//!  1      side (Accepted) or reason (Rejected)
//!  2..4   reserved
//!  4..8   price     (Accepted, Fill)
//!  8..16  a         id (Accepted/Rested/Expired/Cancelled/Reduced), taker (Fill)
//! 16..24  b         qty (Accepted/Rested/Expired/Cancelled), maker (Fill), from (Reduced)
//! 24..32  c         qty (Fill), to (Reduced)
//! ```
//!
//! A response batch is a 16-byte header `[cmd_seq u64][n_events u32][0u32]`
//! followed by `n_events` event records.

use vmatch_core::{Command, Event, OrdType, RejectReason, Side, Tif};

pub const CMD_LEN: usize = 24;
pub const EVT_LEN: usize = 32;
pub const BATCH_HDR_LEN: usize = 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    BadKind(u8),
    BadSide(u8),
    BadOrdType(u8),
    BadTif(u8),
}

fn side_from(b: u8) -> Result<Side, DecodeError> {
    match b {
        0 => Ok(Side::Buy),
        1 => Ok(Side::Sell),
        x => Err(DecodeError::BadSide(x)),
    }
}

fn side_to(s: Side) -> u8 {
    match s {
        Side::Buy => 0,
        Side::Sell => 1,
    }
}

fn tif_to(t: Tif) -> u8 {
    match t {
        Tif::Gtc => 0,
        Tif::Ioc => 1,
        Tif::Fok => 2,
        Tif::PostOnly => 3,
    }
}

pub fn reason_code(r: RejectReason) -> u8 {
    match r {
        RejectReason::InvalidPrice => 1,
        RejectReason::InvalidQty => 2,
        RejectReason::InvalidTif => 3,
        RejectReason::BookFull => 4,
        RejectReason::SeqExhausted => 5,
        RejectReason::UnknownOrder => 6,
        RejectReason::WouldCross => 7,
        RejectReason::FokUnfillable => 8,
    }
}

pub fn reason_from(b: u8) -> Option<RejectReason> {
    Some(match b {
        1 => RejectReason::InvalidPrice,
        2 => RejectReason::InvalidQty,
        3 => RejectReason::InvalidTif,
        4 => RejectReason::BookFull,
        5 => RejectReason::SeqExhausted,
        6 => RejectReason::UnknownOrder,
        7 => RejectReason::WouldCross,
        8 => RejectReason::FokUnfillable,
        _ => return None,
    })
}

#[inline]
fn u32_at(b: &[u8], i: usize) -> u32 {
    u32::from_le_bytes(b[i..i + 4].try_into().unwrap())
}

#[inline]
fn u64_at(b: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(b[i..i + 8].try_into().unwrap())
}

pub fn decode_command(b: &[u8; CMD_LEN]) -> Result<Command, DecodeError> {
    let price = u32_at(b, 4);
    let qty = u64_at(b, 8);
    let id = u64_at(b, 16);
    match b[0] {
        1 => {
            let side = side_from(b[1])?;
            let ord_type = match b[2] {
                0 => OrdType::Limit,
                1 => OrdType::Market,
                x => return Err(DecodeError::BadOrdType(x)),
            };
            let tif = match b[3] {
                0 => Tif::Gtc,
                1 => Tif::Ioc,
                2 => Tif::Fok,
                3 => Tif::PostOnly,
                x => return Err(DecodeError::BadTif(x)),
            };
            Ok(Command::New { side, ord_type, tif, price, qty })
        }
        2 => Ok(Command::Cancel { id }),
        3 => {
            let post_only = match b[1] {
                0 => false,
                1 => true,
                x => return Err(DecodeError::BadSide(x)),
            };
            Ok(Command::Replace { id, price, qty, post_only })
        }
        x => Err(DecodeError::BadKind(x)),
    }
}

pub fn encode_command(c: &Command) -> [u8; CMD_LEN] {
    let mut b = [0u8; CMD_LEN];
    match *c {
        Command::New { side, ord_type, tif, price, qty } => {
            b[0] = 1;
            b[1] = side_to(side);
            b[2] = match ord_type {
                OrdType::Limit => 0,
                OrdType::Market => 1,
            };
            b[3] = tif_to(tif);
            b[4..8].copy_from_slice(&price.to_le_bytes());
            b[8..16].copy_from_slice(&qty.to_le_bytes());
        }
        Command::Cancel { id } => {
            b[0] = 2;
            b[16..24].copy_from_slice(&id.to_le_bytes());
        }
        Command::Replace { id, price, qty, post_only } => {
            b[0] = 3;
            b[1] = post_only as u8;
            b[4..8].copy_from_slice(&price.to_le_bytes());
            b[8..16].copy_from_slice(&qty.to_le_bytes());
            b[16..24].copy_from_slice(&id.to_le_bytes());
        }
    }
    b
}

pub fn encode_event(e: &Event, out: &mut [u8; EVT_LEN]) {
    *out = [0u8; EVT_LEN];
    let (kind, sb, price, a, bb, c) = match *e {
        Event::Accepted { id, side, price, qty } => (1u8, side_to(side), price, id, qty, 0),
        Event::Fill { taker, maker, price, qty } => (2, 0, price, taker, maker, qty),
        Event::Rested { id, qty } => (3, 0, 0, id, qty, 0),
        Event::Expired { id, qty } => (4, 0, 0, id, qty, 0),
        Event::Cancelled { id, qty } => (5, 0, 0, id, qty, 0),
        Event::Reduced { id, from, to } => (6, 0, 0, id, from, to),
        Event::Rejected { reason } => (7, reason_code(reason), 0, 0, 0, 0),
    };
    out[0] = kind;
    out[1] = sb;
    out[4..8].copy_from_slice(&price.to_le_bytes());
    out[8..16].copy_from_slice(&a.to_le_bytes());
    out[16..24].copy_from_slice(&bb.to_le_bytes());
    out[24..32].copy_from_slice(&c.to_le_bytes());
}

pub fn decode_event(b: &[u8; EVT_LEN]) -> Option<Event> {
    let price = u32_at(b, 4);
    let a = u64_at(b, 8);
    let bb = u64_at(b, 16);
    let c = u64_at(b, 24);
    Some(match b[0] {
        1 => Event::Accepted { id: a, side: side_from(b[1]).ok()?, price, qty: bb },
        2 => Event::Fill { taker: a, maker: bb, price, qty: c },
        3 => Event::Rested { id: a, qty: bb },
        4 => Event::Expired { id: a, qty: bb },
        5 => Event::Cancelled { id: a, qty: bb },
        6 => Event::Reduced { id: a, from: bb, to: c },
        7 => Event::Rejected { reason: reason_from(b[1])? },
        _ => return None,
    })
}

/// Append a response batch (header + events) to `buf`.
pub fn encode_batch(cmd_seq: u64, events: &[Event], buf: &mut Vec<u8>) {
    buf.extend_from_slice(&cmd_seq.to_le_bytes());
    buf.extend_from_slice(&(events.len() as u32).to_le_bytes());
    buf.extend_from_slice(&0u32.to_le_bytes());
    let mut rec = [0u8; EVT_LEN];
    for e in events {
        encode_event(e, &mut rec);
        buf.extend_from_slice(&rec);
    }
}

/// Structural equality for core types (the core avoids deriving `PartialEq`
/// so that equality stays out of the verified surface).
pub fn event_eq(a: &Event, b: &Event) -> bool {
    let mut x = [0u8; EVT_LEN];
    let mut y = [0u8; EVT_LEN];
    encode_event(a, &mut x);
    encode_event(b, &mut y);
    x == y
}

pub fn command_eq(a: &Command, b: &Command) -> bool {
    encode_command(a) == encode_command(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn command_roundtrip() {
        let cmds = [
            Command::New { side: Side::Buy, ord_type: OrdType::Limit, tif: Tif::Gtc, price: 7, qty: 9 },
            Command::New { side: Side::Sell, ord_type: OrdType::Market, tif: Tif::Fok, price: 0, qty: u64::MAX },
            Command::Cancel { id: 0xdead_beef },
            Command::Replace { id: 42, price: 3, qty: 5, post_only: true },
        ];
        for c in &cmds {
            let d = decode_command(&encode_command(c)).unwrap();
            assert!(command_eq(c, &d));
        }
    }

    #[test]
    fn event_roundtrip() {
        let evs = [
            Event::Accepted { id: 1, side: Side::Sell, price: 2, qty: 3 },
            Event::Fill { taker: 1, maker: 2, price: 3, qty: 4 },
            Event::Rested { id: 1, qty: 2 },
            Event::Expired { id: 1, qty: 2 },
            Event::Cancelled { id: 1, qty: 2 },
            Event::Reduced { id: 1, from: 9, to: 2 },
            Event::Rejected { reason: RejectReason::FokUnfillable },
        ];
        let mut rec = [0u8; EVT_LEN];
        for e in &evs {
            encode_event(e, &mut rec);
            assert!(event_eq(e, &decode_event(&rec).unwrap()));
        }
    }

    #[test]
    fn rejects_malformed() {
        let mut b = [0u8; CMD_LEN];
        b[0] = 9;
        assert_eq!(decode_command(&b).unwrap_err(), DecodeError::BadKind(9));
        b[0] = 1;
        b[1] = 2;
        assert_eq!(decode_command(&b).unwrap_err(), DecodeError::BadSide(2));
    }
}
