# business-days

business-days adds helper functions to easily work with business days and holidays. This crate currently focuses on adding such functionality to [jiff](https://crates.io/crates/jiff), but it should be possible to extend this crate to support other date/time libraries in Rust.

Currently business-days provides an implementation of the US holidays through the `UsCalendar` type. Alternative calendars can be implemented by implementing the `Calendar` trait.
