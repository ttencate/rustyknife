use std::ops::*;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub struct Bit(u8);

#[allow(dead_code)]
pub const BIT0: Bit = Bit(0);
#[allow(dead_code)]
pub const BIT1: Bit = Bit(1);
#[allow(dead_code)]
pub const BIT2: Bit = Bit(2);
#[allow(dead_code)]
pub const BIT3: Bit = Bit(3);
#[allow(dead_code)]
pub const BIT4: Bit = Bit(4);
#[allow(dead_code)]
pub const BIT5: Bit = Bit(5);
#[allow(dead_code)]
pub const BIT6: Bit = Bit(6);
#[allow(dead_code)]
pub const BIT7: Bit = Bit(7);
#[allow(dead_code)]
pub const BIT8: Bit = Bit(8);
#[allow(dead_code)]
pub const BIT9: Bit = Bit(9);
#[allow(dead_code)]
pub const BIT10: Bit = Bit(10);
#[allow(dead_code)]
pub const BIT11: Bit = Bit(11);
#[allow(dead_code)]
pub const BIT12: Bit = Bit(12);
#[allow(dead_code)]
pub const BIT13: Bit = Bit(13);
#[allow(dead_code)]
pub const BIT14: Bit = Bit(14);
#[allow(dead_code)]
pub const BIT15: Bit = Bit(15);

impl Bit {
    pub fn number(num: u8) -> Bit {
        Bit(num)
    }

    fn mask<T>(self) -> T
        where T: Shl<Output = T> + From<u8>
    {
        let one: T = T::from(1u8);
        one << T::from(self.0)
    }
}

impl Add<u8> for Bit {
    type Output = Bit;
    fn add(self, offset: u8) -> Bit {
        Bit(self.0 + offset)
    }
}

pub trait Bits {
    fn bit(self, bit: Bit) -> bool;
    fn set_bit(self, bit: Bit, value: bool) -> Self;

    fn bits(self, range: RangeInclusive<Bit>) -> Self;
}

impl<T> Bits for T
    where T : Shl<Output = T> + Shr<Output = T> + BitAnd<Output = T> + BitOr<Output = T> + Not<Output = T> + Sub<Output = T> + PartialEq + From<u8>
{
    fn bit(self, bit: Bit) -> bool {
        assert!(bit.mask::<Self>() != Self::from(0));
        self & bit.mask() != Self::from(0)
    }

    fn set_bit(self, bit: Bit, value: bool) -> Self {
        if value {
            self | bit.mask::<Self>()
        } else {
            self & !bit.mask::<Self>()
        }
    }

    fn bits(self, range: RangeInclusive<Bit>) -> Self {
        if range.start() > range.end() {
            return Self::from(0);
        }
        let s = *range.start();
        let e = *range.end();
        assert!(s.mask::<Self>() != Self::from(0));
        assert!(e.mask::<Self>() != Self::from(0));
        (self >> Self::from(s.0)) & ((Self::from(1u8) << Self::from(e.0 + 1 - s.0)) - Self::from(1))
    }
}
