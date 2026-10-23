//! Proof-It engine: orchestration of all analyses, the attack engine,
//! change assurance (affected properties, regressions, merge policy) and reports.

pub mod appchecks;
pub mod attack;
pub mod change;
pub mod coverage;
pub mod datafiles;
pub mod exec;
pub mod external;
pub mod pipeline;
pub mod reachable;
pub mod report;
pub mod runtime;
pub mod secrets;
pub mod selftest;
pub mod verdict;
