#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

pub mod contracts;
pub mod engine;
pub mod prepass;
pub mod report;
