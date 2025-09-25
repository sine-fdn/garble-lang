# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.7.0-alpha.1]

### Changed
- Change `Circuit::wires` into an Iterator ([#210])
- Change for-join loop `join` call to `join_iter` ([#213])
- Change `GarbleProgram.circuit` type to `CircuitType` enum

### Fixed
- Fix `join_iter` for duplicate inputs ([#231])

### Added
- Add `Circuit::wires_len() -> usize` ([#210])
- Implement [`JsonSchema`](https://docs.rs/schemars/0.9.0/schemars/trait.JsonSchema.html) for `Literal` ([#216])
- Support arrays with a const expr size ([#220])
- Implement `From<T> for Literal` for more `T`s ([#229])
- Add `garble_consts!` macro for easy const declaration ([#230])
- Add `register_circuit` module with Circuit comprising register-based instructions ([#232]) 
