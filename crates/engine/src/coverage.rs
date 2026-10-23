//! Coverage of recognised security catalogues (OWASP Top 10, OWASP API Top 10,
//! CWE Top 25): what Proof-It proves, detects, delegates, or does not cover.

use proof_it_core::property::{COVERAGE, Registry};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Coverage {
    pub catalogues: Vec<Catalogue>,
}

#[derive(Debug, Deserialize)]
pub struct Catalogue {
    pub name: String,
    pub items: Vec<Item>,
}

#[derive(Debug, Deserialize)]
pub struct Item {
    pub id: String,
    pub title: String,
    pub how: String,
    #[serde(default)]
    pub rules: Vec<String>,
    #[serde(default)]
    pub gaps: Option<String>,
    #[serde(default)]
    pub why: Option<String>,
}

pub fn load() -> Coverage {
    serde_saphyr::from_str(COVERAGE).unwrap_or(Coverage { catalogues: vec![] })
}

/// Every rule id Proof-It can emit (plus property ids and external-tool prefixes).
pub fn known_rules(reg: &Registry) -> Vec<String> {
    let mut v: Vec<String> = proof_it_lang_ts::security::RULES.iter().map(|r| r.id.to_owned()).collect();
    v.extend(proof_it_lang_ts::static_checks::RULE_IDS.iter().map(|s| (*s).to_owned()));
    v.extend(crate::secrets::rule_ids().into_iter().map(str::to_owned));
    v.push(crate::datafiles::RULE_ID.to_owned());
    v.extend(crate::appchecks::RULE_IDS.iter().map(|s| (*s).to_owned()));
    v.extend(crate::runtime::RULE_IDS.iter().map(|s| (*s).to_owned()));
    v.extend(reg.properties.keys().cloned());
    v.extend(["osv:", "gitleaks:", "semgrep:"].iter().map(|s| (*s).to_owned()));
    v
}

/// Fraction of catalogue items with at least some coverage, per catalogue.
pub fn summary(c: &Coverage) -> Vec<(String, usize, usize, usize)> {
    c.catalogues
        .iter()
        .map(|cat| {
            let full = cat.items.iter().filter(|i| matches!(i.how.as_str(), "proven" | "detected" | "external")).count();
            let partial = cat.items.iter().filter(|i| i.how == "partial").count();
            (cat.name.clone(), full, partial, cat.items.len())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn property_detectors_exist() {
        let reg = Registry::load(None).expect("library");
        let known = known_rules(&reg);
        for p in reg.properties.values() {
            for d in &p.spec.detectors {
                let ok = known.iter().any(|k| k == d) || (d.ends_with('*') && known.iter().any(|k| k.starts_with(d.trim_end_matches('*'))));
                assert!(ok, "{}: detector {d} does not exist", p.id());
            }
        }
    }

    #[test]
    fn coverage_matrix_cites_only_real_rules() {
        let reg = Registry::load(None).expect("library");
        let known = known_rules(&reg);
        let c = load();
        assert!(c.catalogues.len() >= 3, "coverage.yaml failed to parse");
        for cat in &c.catalogues {
            for it in &cat.items {
                assert!(matches!(it.how.as_str(), "proven" | "detected" | "external" | "partial" | "none"), "{}: bad `how`", it.id);
                if it.how == "none" {
                    assert!(it.why.is_some(), "{}: `none` needs a `why`", it.id);
                }
                for r in &it.rules {
                    assert!(known.iter().any(|k| k == r), "{} {}: unknown rule {r}", cat.name, it.id);
                }
            }
        }
    }
}
