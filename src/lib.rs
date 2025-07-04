use jiff::civil::{date, Date, Weekday};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    TryFromInt(#[from] std::num::TryFromIntError),
    #[error("{0}")]
    Computus(&'static str),
    #[error(transparent)]
    Jiff(#[from] jiff::Error),
}

type HolidayDate = fn(i16) -> Result<Date, Error>;

/// Martin Luther King Day is on the 3th Monday of January.
pub fn get_martin_luther_king_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 1, 1).nth_weekday_of_month(3, Weekday::Monday)?)
}

/// President's Day is on the 3th Monday of February.
pub fn get_president_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 2, 1).nth_weekday_of_month(3, Weekday::Monday)?)
}

/// Labor Day is on the 1st Monday of September.
pub fn get_labor_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 9, 1).nth_weekday_of_month(1, Weekday::Monday)?)
}

/// Columbus Day is on the 2nd Monday of October.
pub fn get_columbus_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 10, 1).nth_weekday_of_month(2, Weekday::Monday)?)
}

/// Thanksgiving Day is on the 4th Thursday of November.
pub fn get_thanksgiving_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 11, 1).nth_weekday_of_month(4, Weekday::Thursday)?)
}

/// Thanksgiving has a bridge day on the Friday after Thanksgiving.
pub fn get_thanksgiving_bridge_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 11, 1).nth_weekday_of_month(4, Weekday::Friday)?)
}

/// New Years Day is on the 1st of January.
pub fn get_new_years_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 1, 1))
}

/// Juneteenth is on the 19th of June.
pub fn get_juneteenth(year: i16) -> Result<Date, Error> {
    Ok(date(year, 6, 19))
}

/// The Day before Independence Day is on the 3th of July.
pub fn get_day_before_independence_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 7, 3))
}

/// Independence Day is on the 4th of July.
pub fn get_independence_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 7, 4))
}

/// Veteran's Day is on the 11th of November.
pub fn get_veterans_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 11, 11))
}

/// Christmas Eve is the day before Christmas Day.
pub fn get_christmas_eve(year: i16) -> Result<Date, Error> {
    Ok(date(year, 12, 24))
}

/// Christmas Day is on the 25th of December.
pub fn get_christmas_day(year: i16) -> Result<Date, Error> {
    Ok(date(year, 12, 25))
}

/// Memorial Day is on the last Monday of May.
pub fn get_memorial_day(year: i16) -> Result<Date, Error> {
    let mut date = date(year, 5, 31);

    while date.weekday() != Weekday::Monday {
        date = date.yesterday()?;
    }

    Ok(date)
}

/// Easter Day is calculated using the Computus method.
pub fn get_easter(year: i16) -> Result<Date, Error> {
    let easter = computus::gregorian(year.into()).map_err(Error::Computus)?;

    Ok(date(
        easter.year.try_into()?,
        easter.month.try_into()?,
        easter.day.try_into()?,
    ))
}

/// Good Friday is two days before Easter Day (Sunday).
pub fn get_good_friday(year: i16) -> Result<Date, Error> {
    get_easter(year)
        .and_then(|easter| easter.yesterday().map_err(Error::Jiff))
        .and_then(|saturday| saturday.yesterday().map_err(Error::Jiff))
}

#[derive(Clone, Debug)]
pub enum Holiday<T: Clone + std::fmt::Debug + std::fmt::Display> {
    Holiday(T),
    Observed(T),
}

impl<T: Clone + std::fmt::Debug + std::fmt::Display> std::fmt::Display for Holiday<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::Holiday(holiday) => write!(f, "{holiday}"),
            Self::Observed(holiday) => write!(f, "{holiday} (Observed)"),
        }
    }
}

impl<T: Clone + std::fmt::Debug + std::fmt::Display> Holiday<T> {
    /// Returns `true` if the holiday is an actual holiday. Returns `false` otherwise.
    pub fn is_holiday(&self) -> bool {
        matches!(self, Self::Holiday(..))
    }

    /// Returns `true` if the holiday is observed. Returns `false` otherwise.
    pub fn is_observed(&self) -> bool {
        matches!(self, Self::Observed(..))
    }
}

pub trait Calendar<T: Clone + std::fmt::Debug + std::fmt::Display + 'static> {
    /// The array of functions used to calculate the date of a holiday for a given year.
    const HOLIDAYS: &[(HolidayDate, T)];

    /// Returns `true` if the given date is on a weekday. Returns `false` otherwise.
    fn is_weekday(&self, date: Date) -> bool;

    /// Returns `true` if the given date is on a weekend. Returns `false` otherwise.
    fn is_weekend(&self, date: Date) -> bool {
        !self.is_weekday(date)
    }

    /// Returns the next consecutive weekday.
    fn next_weekday(&self, date: Date) -> Result<Date, Error> {
        let mut next = date.tomorrow()?;

        while self.is_weekend(next) {
            next = next.tomorrow()?;
        }

        Ok(next)
    }

    /// Returns the previous consecutive weekday.
    fn previous_weekday(&self, date: Date) -> Result<Date, Error> {
        let mut previous = date.yesterday()?;

        while self.is_weekend(previous) {
            previous = previous.yesterday()?;
        }

        Ok(previous)
    }

    /// Returns the observance day for a given date on which that date would be observed, i.e. the
    /// closest weekday to the given date if the date is on a weekend.
    fn get_observance_day(&self, date: Date) -> Result<Date, Error> {
        let mut previous = date;
        let mut next = date;

        while self.is_weekend(previous) && self.is_weekend(next) {
            previous = previous.yesterday()?;
            next = next.tomorrow()?;
        }

        Ok(if self.is_weekday(previous) {
            previous
        } else {
            next
        })
    }

    /// Returns whether the given date has a holiday or an observed holiday.
    fn get_holiday(&self, date: Date) -> Option<Holiday<T>> {
        for (f, result) in Self::HOLIDAYS {
            let Ok(holiday) = f(date.year()) else {
                continue;
            };

            if holiday == date {
                return Some(Holiday::Holiday(result.clone()));
            }

            let Ok(holiday) = self.get_observance_day(holiday) else {
                continue;
            };

            if holiday == date {
                return Some(Holiday::Observed(result.clone()));
            }
        }

        None
    }

    /// Returns `true` if the given date is a holiday. Returns `false` otherwise.
    fn is_holiday(&self, date: Date) -> bool {
        self.get_holiday(date)
            .map(|holiday| holiday.is_holiday())
            .unwrap_or(false)
    }

    /// Returns `true` if the given date is the observance day for a holiday. Returns `false`
    /// otherwise.
    fn is_observed_holiday(&self, date: Date) -> bool {
        self.get_holiday(date)
            .map(|holiday| holiday.is_observed())
            .unwrap_or(false)
    }

    /// Returns `true` if the given date is a business day, i.e., if the given date is neither a
    /// holiday nor the observance day for a holiday. Returns `false` otherwise.
    fn is_business_day(&self, date: Date) -> bool {
        self.is_weekday(date) && self.get_holiday(date).is_none()
    }

    /// Returns the next consecutive business day for the given date.
    fn next_business_day(&self, date: Date) -> Result<Date, Error> {
        let mut next = date.tomorrow()?;

        while !self.is_business_day(next) {
            next = next.tomorrow()?;
        }

        Ok(next)
    }

    /// Returns the previous consecutive business day for the given date.
    fn previous_business_day(&self, date: Date) -> Result<Date, Error> {
        let mut previous = date.yesterday()?;

        while !self.is_business_day(previous) {
            previous = previous.yesterday()?;
        }

        Ok(previous)
    }

    /// Returns `true` if the given date is a bridge day, i.e., a day that falls between a holiday
    /// and the weekend. Returns `false` otherwise.
    fn is_bridge_day(&self, date: Date) -> bool {
        let is_prev_non_business = date
            .yesterday()
            .map(|date| !self.is_business_day(date))
            .unwrap_or(false);
        let is_next_non_business = date
            .tomorrow()
            .map(|date| !self.is_business_day(date))
            .unwrap_or(false);

        is_prev_non_business && is_next_non_business
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UsHoliday {
    NewYear,
    MartinLutherKingDay,
    PresidentDay,
    GoodFriday,
    Easter,
    IndependenceDay,
    MemorialDay,
    Juneteenth,
    LaborDay,
    ColumbusDay,
    VeteransDay,
    Thanksgiving,
    Christmas,
}

impl std::fmt::Display for UsHoliday {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::NewYear => "New Year",
                Self::MartinLutherKingDay => "Martin Luther King Day",
                Self::PresidentDay => "President's Day",
                Self::GoodFriday => "Good Friday",
                Self::Easter => "Easter",
                Self::IndependenceDay => "Independence Day",
                Self::MemorialDay => "Memorial Day",
                Self::Juneteenth => "Juneteenth",
                Self::LaborDay => "Labor Day",
                Self::ColumbusDay => "Columbus Day",
                Self::VeteransDay => "Veterans Day",
                Self::Thanksgiving => "Thanksgiving",
                Self::Christmas => "Christmas",
            }
        )
    }
}

pub struct UsCalendar;

impl Calendar<UsHoliday> for UsCalendar {
    const HOLIDAYS: &[(HolidayDate, UsHoliday)] = &[
        (get_new_years_day, UsHoliday::NewYear),
        (get_martin_luther_king_day, UsHoliday::MartinLutherKingDay),
        (get_president_day, UsHoliday::PresidentDay),
        (get_good_friday, UsHoliday::GoodFriday),
        (get_easter, UsHoliday::Easter),
        (get_independence_day, UsHoliday::IndependenceDay),
        (get_memorial_day, UsHoliday::MemorialDay),
        (get_juneteenth, UsHoliday::Juneteenth),
        (get_labor_day, UsHoliday::LaborDay),
        (get_columbus_day, UsHoliday::ColumbusDay),
        (get_veterans_day, UsHoliday::VeteransDay),
        (get_thanksgiving_day, UsHoliday::Thanksgiving),
        (get_christmas_day, UsHoliday::Christmas),
    ];

    fn is_weekday(&self, date: Date) -> bool {
        matches!(
            date.weekday(),
            Weekday::Monday
                | Weekday::Tuesday
                | Weekday::Wednesday
                | Weekday::Thursday
                | Weekday::Friday
        )
    }
}
