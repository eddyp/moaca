
/// the core (or system?) emulator structure
/// we start initially with the rv32i base ISA
pub(crate) struct Emu {
    regs: [u32; 32],
    pc: u32,
}

#[repr(usize)]
pub enum Register {
    Zero = 0,
    Ra, // Return address
    Sp, // Stack pointer
    Gp, // Global pointer
    Tp, //Thread pointer
    T0, // Temporary/alternate link register
    T1, // Temporary
    T2, // Temporary
    S0Fp, // Saved register / Frame pointer
    S1, // Saved register 1
    A0, // Function argument 0 / Return value
    A1, // Function argument 1 / Return value
    A2, // Function argument 2
    A3, // Function argument 3
    A4, // Function argument 4
    A5, // Function argument 5 / x15
    A6, // Function argument 6 / x16
    A7, // Function argument 7
    S2, // Saved register 2
    S3, // Saved register 3
    S4, // Saved register 4
    S5, // Saved register 5
    S6, // Saved register 6
    S7, // Saved register 7
    S8, // Saved register 8
    S9, // Saved register 9
    S10, // Saved register 10
    S11, // Saved register 11
    T3, // Temporary register 3
    T4, // Temporary register 4
    T5, // Temporary register 5
    T6, // Temporary register 6
}

impl From<u32> for Register {
    fn from(index:u32) -> Self {
        assert!(index < 32);
        // SAFETY: the value is definitely in the range [0-32)
        // doesn't make sense to do any bit masking as that would be a costly operation,
        // and the input is already a valid representation value for Register
        unsafe {
            core::ptr::read_unaligned(&(index as usize)
                as *const usize
                as *const Register) }
    }
}

impl Emu {
    pub fn new() -> Self {
        Self {
            regs: [0; 32],
            pc: 0,
        }
    }

    pub fn pc(&self) -> u32 {
        self.pc
    }

    pub fn get_reg(&self, reg_index: u32) -> u32 {
        self.regs[Register::from(reg_index) as usize]
    }
}

/// RV32I instruction types: R, I, S or U
struct Rtype {}
struct Itype {}
struct Stype {}
struct Utype {}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let emu = Emu::new();
        assert_eq!(emu.pc(), 0);
        assert_eq!(emu.get_reg(0), 0);
    }
}
