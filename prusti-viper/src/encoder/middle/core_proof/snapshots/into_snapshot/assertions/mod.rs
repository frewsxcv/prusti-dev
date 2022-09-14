/// Assertions that are self-framing: each dereference of a pointer needs to be
/// behind `own`.
mod self_framing;
/// Assertions where the places (leaves) are translated to `snap` calls.
mod snap;
/// Assertions where the places are translated by using `heap$` pure variable.
mod pure_heap;

pub(in super::super::super::super) use self_framing::SelfFramingAssertionToSnapshot;
