# Change Log

All notable changes to this project will be documented in this file.
This project adheres to [Semantic Versioning](http://semver.org/).
This file follows the convention described at
[Keep a Changelog](http://keepachangelog.com/en/1.0.0/).

## [1.0.3] - 2025-11-05
### Fixed
- Out of bounds panic in `IntoIterator` drop implementation.

## [1.0.2] - 2025-11-01
### Fixed
- Crash when dropping an empty `IntoIterator`.

## [1.0.1] - 2025-09-24
### Changed
- Use arithmetic to compute data block capacity for a `d` value (vs a loop).

## [1.0.0] - 2025-08-24
### Changed
- Initial release
