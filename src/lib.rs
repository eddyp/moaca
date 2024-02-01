
use std::fs;
use std::path::Path;

/// the core (or system?) emulator structure
/// we start initially with the rv32i base ISA
pub struct Emu {
    regs: [u32; 32],
    pc: u32,
    memory: Vec<u8>,
    csr: Vec<u8>,
}

#[derive(Debug, PartialEq)]
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
    pub fn new(size: usize) -> Self {
        Self {
            regs: [0; 32],
            pc: 0,
            memory: vec![0; size],
            csr: vec![0; 4096],
        }
    }

    pub fn new_from_file(filename: &str, base: usize) -> Self {
        if let Some(memory) = Self::load_memory_vec_from_file(filename, base) {
            Self {
                regs: [0; 32],
                pc: 0,
                memory,
                csr: vec![0; 4096],
            }
        } else {
            panic!("Can't load memory from file {filename} at offset {base}");
        }
    }

    pub fn new_from_vec(mut memory: Vec<u8>, base: usize) -> Self {
        let len = memory.len();
        assert!(len >= 4);
        let memory = if base == 0 {
            memory
        } else {
            let mut mem = vec![0;base + len];
            mem.truncate(base);
            mem.append(&mut memory);

            mem
        };

        Self {
            regs: [0; 32],
            pc: 0,
            memory,
            csr: vec![0; 4096],
        }
    }


    pub fn pc(&self) -> u32 {
        self.pc
    }

    pub fn set_pc(&mut self, pc: u32) {
        assert!(pc < self.memory.len() as u32);
        self.pc = pc;
    }

    pub fn get_reg_x(&self, reg_index: u32) -> u32 {
        self.regs[Register::from(reg_index) as usize]
    }

    pub fn get_reg(&self, reg_id: Register) -> u32 {
        self.regs[reg_id as usize]
    }

    fn load_memory_vec_from_file(raw_binary_file: &str, base: usize) -> Option<Vec<u8>> {
        let file_name = Path::new(raw_binary_file);
        if file_name.is_file() {
            let mut contents = fs::read(raw_binary_file).ok()?;
            let mut memory = vec![0u8; base];

            memory.reserve_exact(contents.len());
            memory.append(&mut contents);

            Some(memory)
        } else {
            None
        }
    }

    pub fn execute(&mut self, steps: usize) {
        let mut found_unkown_opcodes = 0usize;

        for _ in 0..steps {
            let pc = self.pc() as usize;
            let instr_bytes: [u8; 4] = if let Ok(four_bytes) = &(self.memory[pc..(pc+4)]).try_into() {
                *four_bytes
            } else {
                panic!("Not enough bytes in memory to read one instruction a address 0x{pc:08X}!")
            };

            let instruction = u32::from_le_bytes(instr_bytes);

            let opcode = instruction & OPCODE_MASK;

            match opcode {
                0b1101111 => { /* JAL - Jtype ( Utype?) */
                    let jal = Jtype::from(instruction);

                    let offset = jal.offset;
                    if Register::Zero != jal.rd {
                        self.regs[jal.rd as usize] = self.pc + 4;
                    }
                    self.set_pc((pc as i32 + offset) as u32);
                },
                0b0110111 => { /* LUI - U type */
                    let lui = Utype::from(instruction);

                    if lui.rd != Register::Zero {
                        self.regs[lui.rd as usize] = lui.imm31_12;
                    } else {
                        panic!("Don't know what LUI X0, IMM should do!");
                    }

                    self.pc += 4;
                },
                0b0010011 => { /* I-type instructions - ADDI, SLTI... */
                    let itype = Itype::from(instruction);

                    let subtype = itype.funct3;

                    match subtype {
                        0b000 => {
                            /* ADDI */
                            let rs1_i32 = self.get_reg(itype.rs1) as i32;
                            let imm_i32 = itype.imm11_0 as i32;
                            let rd = rs1_i32.wrapping_add(imm_i32);

                            self.regs[itype.rd as usize] = rd as u32;
                        },
                        _ => {
                            eprintln!("Ignored Itype {subtype} 0x{opcode:02X} / 0b{opcode:07b} @ address 0x{pc:08X}");
                            found_unkown_opcodes += 1;
                        }
                    };
                    self.pc += 4;

                },
                /* Zicsr */
                0b1110011 => { /* SYSTEM / CSR* */
                    let itype = Itype::from(instruction);
                    let subtype = itype.funct3;

                    match subtype {
                        0b001 => { // CSRRW
                            eprintln!("Ignorring CSRRW ({subtype}) @ address 0x{pc:08X}");
                        },
                        _ => {
                            eprintln!("Ignored SYSTEM {subtype} 0x{opcode:02X} / 0b{opcode:07b} @ address 0x{pc:08X}");
                            found_unkown_opcodes += 1;
                        },
                    };
                    self.pc += 4;

                },
                _ =>  {
                    eprintln!("Ignoring unhandled opcode 0x{opcode:02X} / 0b{opcode:07b} @ address 0x{pc:08X}");
                    found_unkown_opcodes += 1;
                    self.pc += 4;
                },
                // _ => panic!("Don't know how to decode opcode 0x{opcode:02X} / 0b{opcode:07b}"),

            }
        }
        if found_unkown_opcodes > 0 {
            panic!("Skipped {found_unkown_opcodes} instructions with unknown opcodes after {steps} steps. Stopping!");
        }
    }

}

/// RV32I instruction types: R, I, S or U
///
const MASK_3_BITS: u32 = 0b0000_0111;
const MASK_5_BITS: u32 = 0b0001_1111;
const MASK_7_BITS: u32 = 0b0111_1111;
const MASK_8_BITS: u32 = 0b1111_1111;
const MASK_10_BITS: u32 = 0b0011_1111_1111;
const MASK_12_BITS: u32 = 0b1111_1111_1111;
const MASK_20_BITS: u32 = 0b1111_1111_1111_1111_1111;

// shifts for the instruction fields
const RD_SHIFT: usize = 7;
const IMM_4_0_SHIFT: usize = 7;
const FUNCT3_SHIFT: usize = 12;
const IMM_31_12_SHIFT: usize = 12;
const RS1_SHIFT: usize = 15;
const RS2_SHIFT: usize = 20;
const IMM_11_0_SHIFT: usize = 20;
const FUNCT7_SHIFT: usize = 25;
const IMM_11_5_SHIFT: usize = 25;


// masks for the instruction fields
const OPCODE_MASK: u32 = MASK_7_BITS;
const RD_MASK: u32 = MASK_5_BITS << RD_SHIFT;
const RS1_MASK: u32 = MASK_5_BITS << RS1_SHIFT;
const RS2_MASK: u32 = MASK_5_BITS << RS2_SHIFT;
const FUNCT3_MASK: u32 = MASK_3_BITS << FUNCT3_SHIFT;
const FUNCT7_MASK: u32 = MASK_7_BITS << FUNCT7_SHIFT;
const IMM_4_0_MASK: u32 = MASK_5_BITS << IMM_4_0_SHIFT;
const IMM_11_5_MASK: u32 = MASK_7_BITS << IMM_11_5_SHIFT;
const IMM_11_0_MASK: u32= MASK_12_BITS << IMM_11_0_SHIFT;
const IMM_31_12_MASK: u32 = MASK_20_BITS << IMM_31_12_SHIFT;



struct Rtype {
    rd: Register,
    rs1: Register,
    rs2: Register,
    funct3: u32,
    funct7: u32,
}

impl From<u32> for Rtype {
    fn from(instruction: u32) -> Self {
        let rd = (instruction & RD_MASK) >> RD_SHIFT;
        let rd = Register::from(rd);
        let rs1 = Register::from((instruction & RS1_MASK) >> RS1_SHIFT);
        let rs2 = Register::from((instruction & RS2_MASK) >> RS2_SHIFT);
        let funct3 = (instruction & FUNCT3_MASK) >> FUNCT3_SHIFT;
        let funct7 = (instruction & FUNCT7_MASK) >> FUNCT7_SHIFT;

        Self { rd, rs1, rs2, funct3, funct7 }
    }
}

struct Itype {
    rd: Register,
    rs1: Register,
    funct3: u32,
    imm11_0: u32,
}

impl From<u32> for Itype {
    fn from(instruction: u32) -> Self {
        let rd = (instruction & RD_MASK) >> RD_SHIFT;
        let rd = Register::from(rd);
        let rs1 = Register::from((instruction & RS1_MASK) >> RS1_SHIFT);
        let funct3 = (instruction & FUNCT3_MASK) >> FUNCT3_SHIFT;
        // sign extend the immediate, then treat as u32
        let imm11_0 = (((instruction & IMM_11_0_MASK) as i32)
                                 >> IMM_11_0_SHIFT) as u32;

        Self { rd, rs1, funct3, imm11_0 }
    }
}

struct Stype {
    rs1: Register,
    rs2: Register,
    funct3: u32,
    imm11_0: u32,
}

impl From<u32> for Stype {
    fn from(instruction: u32) -> Self {
        let rs1 = Register::from((instruction & RS1_MASK) >> RS1_SHIFT);
        let rs2 = Register::from((instruction & RS2_MASK) >> RS2_SHIFT);
        let funct3 = (instruction & FUNCT3_MASK) >> FUNCT3_SHIFT;
        let imm11_5 = (((instruction & IMM_11_5_MASK) as i32
                                >> IMM_11_5_SHIFT) as u32) << 5;
        let imm4_0 = (instruction & IMM_4_0_MASK) >> IMM_4_0_SHIFT;
        // sign extend the immediate, then treat as u32
        let imm11_0 = imm11_5 | imm4_0;

        Self { rs1, rs2, funct3, imm11_0 }
    }
}

struct Utype {
    rd: Register,
    imm31_12: u32,
}

impl From<u32> for Utype {
    fn from(instruction: u32) -> Self {
        let rd = (instruction & RD_MASK) >> RD_SHIFT;
        let rd = Register::from(rd);
        // sign extend the immediate, then treat as u32
        let imm31_12 = (((instruction & IMM_31_12_MASK) as i32)
                                >> IMM_31_12_SHIFT) as u32;

        Self { rd, imm31_12 }
    }
}

struct Jtype {
    rd: Register,
    offset: i32,
}

impl From<u32> for Jtype {
    fn from(instruction: u32) -> Self {
        let rd = (instruction & RD_MASK) >> RD_SHIFT;
        let rd = Register::from(rd);

        // the riscv documentation says "j offset" / "jal x0, offset" is
        // jtype and has the order
        // bit   31 |30    21| 20 |19   12|
        //   imm[20 |  10:1  | 11 | 19:12 ]


        // sign extend the immediate
        let instruction = instruction as i32;
        let offset31_20 = (instruction & (0x1 << 31)) >> 31 << 20;

        let offset10_1 = (instruction & ((MASK_10_BITS as i32) << 21)) >> 20;
        let offset11 = (instruction & (0x1 << 20)) >> 20 << 11;
        // bits 19:12 are the same place in offset as they are in the instruction
        let offset19_12 = instruction & ((MASK_8_BITS as i32) << 12);


        let offset = offset31_20 | offset19_12 | offset11 | offset10_1;

        // dbg!("Jtype instruction: {instruction:04X}");
        // dbg!("offset: {offset:04X} : 31:20 {offset31_20:04X} 19:12 {offset19_12:04X} 11 {offset11:04X} 10:1 {offset10_1:04X}");

        Self {rd, offset}
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_emu() {
        let emu = Emu::new(8);
        assert_eq!(emu.pc(), 0);
        for i in 0..32 {
            assert_eq!(emu.get_reg_x(i), 0);
        }
    }

    #[test]
    fn new_emu_from_file_offset_0() {
        let emu = Emu::new_from_file("images/basic.binary", 0);
        assert_eq!(emu.pc(), 0);
        assert_eq!(emu.get_reg_x(0), 0);
        assert_eq!(emu.memory.as_slice().get(0), Some(0x6f).as_ref());
        assert_eq!(emu.memory.as_slice().get(0x124), Some(0x13).as_ref());
    }

    #[test]
    fn new_emu_from_file_offset_0x2000() {
        let emu = Emu::new_from_file("images/basic.binary", 0x2000);
        assert_eq!(emu.pc(), 0);
        assert_eq!(emu.get_reg_x(0), 0);
        assert_eq!(emu.memory.as_slice().get(0x2000), Some(0x6f).as_ref());
        assert_eq!(emu.memory.as_slice().get(0x2124), Some(0x13).as_ref());
        assert_eq!(emu.memory.as_slice().get(0x229c), Some(0x93).as_ref());
    }

    #[test]
    fn new_emu_from_vec() {
        // 6f 00 80 25  	j	+0x258
        // 13 01 41 f7  	addi	sp, sp, -140
        let memory = vec![
            0x6f, 0x00, 0x80, 0x25,
            0x13, 0x01, 0x41, 0xf7,
            ];
        let emu = Emu::new_from_vec(memory, 0);
        assert_eq!(emu.pc(), 0);
        assert_eq!(emu.get_reg_x(0), 0);
        assert_eq!(emu.memory.as_slice().get(0), Some(0x6f).as_ref());
        assert_eq!(emu.memory.as_slice().get(3), Some(0x25).as_ref());
        assert_eq!(emu.memory.as_slice().get(7), Some(0xf7).as_ref());
    }

    #[test]
    fn new_emu_from_vec_offset_0x2000() {
        // 6f 00 80 25  	j	+0x258
        // 13 01 41 f7  	addi	sp, sp, -140
        let memory = vec![
            0x6f, 0x00, 0x80, 0x25,
            0x13, 0x01, 0x41, 0xf7,
            ];
        let emu = Emu::new_from_vec(memory, 0x2000);
        assert_eq!(emu.pc(), 0);
        assert_eq!(emu.get_reg_x(0), 0);
        assert_eq!(emu.memory.as_slice().get(0x2000), Some(0x6f).as_ref());
        assert_eq!(emu.memory.as_slice().get(0x2003), Some(0x25).as_ref());
        assert_eq!(emu.memory.as_slice().get(0x2007), Some(0xf7).as_ref());
    }

    #[test]
    fn set_pc_at_4() {
        let mut emu = Emu::new(8);
        emu.set_pc(4);
        assert_eq!(emu.pc(), 4);
    }

    #[test]
    fn set_pc_at_boot_vector() {
        let mut emu = Emu::new_from_file("images/basic.binary", 0x2000);
        emu.set_pc(0x2000);
        assert_eq!(emu.pc(), 0x2000);
    }

    #[test]
    fn exec_j_start() {
        let mut emu = Emu::new_from_file("images/basic.binary", 0x2000);
        emu.set_pc(0x2000);
        assert_eq!(emu.pc(), 0x2000);

        emu.execute(1usize);
        assert_eq!(emu.pc(), 0x2258);
    }

    #[test]
    fn exec_lui_sp_5() {
        let mut emu = Emu::new_from_file("images/basic.binary", 0x2000);
        emu.set_pc(0x2258);
        let before_pc = emu.pc();
        assert_eq!(before_pc, 0x2258);

        // 2258: 37 51 00 00  	lui	sp, 5
        emu.execute(1usize);
        assert_eq!(emu.get_reg(Register::Sp), 0x5);
        assert_eq!(emu.pc(), before_pc + 4);
    }

    #[test]
    fn exec_addi_a3_zero_52() {
        let mut emu = Emu::new_from_file("images/basic.binary", 0x2000);
        emu.set_pc(0x235c);
        let before_pc = emu.pc();

        // 235c: 93 06 40 03  	addi	a3, zero, 52
        emu.execute(1usize);
        assert_eq!(emu.get_reg(Register::A3), 52);
        assert_eq!(emu.get_reg(Register::Zero), 0x0);
        assert_eq!(emu.pc(), before_pc + 4);
    }

    #[test]
    #[ignore]
    fn exec_multiple_instructions() {
        let mut emu = Emu::new_from_file("images/basic.binary", 0x2000);
        emu.set_pc(0x2000);
        assert_eq!(emu.pc(), 0x2000);
        emu.execute(32);
        assert_ne!(emu.pc(), 0x2258);
    }

    #[test]
    #[should_panic]
    fn set_pc_out_side_mem_panics() {
        let mut emu = Emu::new(8);
        assert_eq!(emu.memory.len(), 8);
        emu.set_pc(12);
    }


    #[test]
    fn rtype_split() {
        // not a real Rtype instruction, but a value easy to test
        let instruction = 0b0000111_00010_00001_011_01101_1111111;

        let rtype = Rtype::from(instruction);

        assert_eq!(rtype.funct3, 3);
        assert_eq!(rtype.funct7, 7);
        assert_eq!(rtype.rs1, 1.into());
        assert_eq!(rtype.rs2, 2.into());
        assert_eq!(rtype.rd, 0x000D.into());
    }

    #[test]
    fn rtype_and_a5_a5_a4() {
        // b3 f7 e7 00  	and	a5, a5, a4
        // 0000000 rs2 rs1 111 rd 0110011
        let instruction = 0x00e7_f7b3;

        let rtype = Rtype::from(instruction);

        assert_eq!(rtype.funct3, 0b111);
        assert_eq!(rtype.funct7, 0);
        assert_eq!(rtype.rs1, Register::A5);
        assert_eq!(rtype.rs2, Register::A4);
        assert_eq!(rtype.rd, Register::A5);
    }

    #[test]
    fn rtype_or_a5_a5_a4() {
        // b3 e7 e7 00  	or	a5, a5, a4
        // 0000000 rs2 rs1 110 rd 0110011
        let instruction = 0x00e7_e7b3;

        let rtype = Rtype::from(instruction);

        assert_eq!(rtype.funct3, 0b110);
        assert_eq!(rtype.funct7, 0);
        assert_eq!(rtype.rs1, Register::A5);
        assert_eq!(rtype.rs2, Register::A4);
        assert_eq!(rtype.rd, Register::A5);
    }

    #[test]
    fn rtype_or_a0_a0_a4() {
        // 33 65 f5 00  	or	a0, a0, a5
        // 0000000 rs2 rs1 110 rd 0110011
        let instruction = 0x00f5_6533;

        let rtype = Rtype::from(instruction);

        assert_eq!(rtype.funct3, 0b110);
        assert_eq!(rtype.funct7, 0);
        assert_eq!(rtype.rs1, Register::A0);
        assert_eq!(rtype.rs2, Register::A5);
        assert_eq!(rtype.rd, Register::A0);
    }

    #[test]
    fn rtype_sub_a0_s0_a0() {
        // 33 05 a4 40  	sub	a0, s0, a0
        // 010000 rs2 rs1 000 rd 0110011
        let instruction = 0x40a4_0533;

        let rtype = Rtype::from(instruction);

        assert_eq!(rtype.funct3, 0b000);
        assert_eq!(rtype.funct7, 0b0100000);
        assert_eq!(rtype.rs1, Register::S0Fp);
        assert_eq!(rtype.rs2, Register::A0);
        assert_eq!(rtype.rd, Register::A0);
    }

    #[test]
    fn itype_addi_sp_sp_m140() {
        // 13 01 41 f7  	addi	sp, sp, -140
        // imm11:0 rs1 000 rd 0010011
        let instruction = 0xf741_0113;

        let itype = Itype::from(instruction);

        assert_eq!(itype.funct3, 0b000);
        assert_eq!(itype.rs1, Register::Sp);
        assert_eq!(itype.rd, Register::Sp);
        assert_eq!(itype.imm11_0, -140i32 as u32);
    }

    #[test]
    fn itype_addi_t0_t0_292() {
        // 93 82 42 12  	addi	t0, t0, 292
        // imm11:0 rs1 000 rd 0010011
        let instruction = 0x1242_8293;

        let itype = Itype::from(instruction);

        assert_eq!(itype.funct3, 0b000);
        assert_eq!(itype.rs1, Register::T0);
        assert_eq!(itype.rd, Register::T0);
        assert_eq!(itype.imm11_0, 292);
    }

    #[test]
    fn itype_andi_a5_s0_15() {
        // 93 f7 f4 00  	andi	a5, s1, 15
        // imm11:0 rs1 111 rd 0010011
        let instruction = 0x00f4_f793;

        let itype = Itype::from(instruction);

        assert_eq!(itype.funct3, 0b111);
        assert_eq!(itype.rs1, Register::S1);
        assert_eq!(itype.rd, Register::A5);
        assert_eq!(itype.imm11_0, 15);
    }

    #[test]
    fn itype_sltiu_a5_a4_26() {
        // 93 37 a7 01  	sltiu	a5, a4, 26
        // imm11:0 rs1 011 rd 0010011
        let instruction =
            u32::from_le_bytes([0x93, 0x37, 0xa7, 0x01]);

        let itype = Itype::from(instruction);

        assert_eq!(itype.funct3, 0b011);
        assert_eq!(itype.rs1, Register::A4);
        assert_eq!(itype.rd, Register::A5);
        assert_eq!(itype.imm11_0, 26);
    }

    #[test]
    fn stype_sw_zero_0_t0() {
        // 23 a0 02 00  	sw	zero, 0(t0)
        // imm11:5 rs2 rs1 010 imm4:0 0100011
        let instruction =
            u32::from_le_bytes([0x23, 0xa0, 0x02, 0x00]);

        let stype = Stype::from(instruction);

        assert_eq!(stype.funct3, 0b010);
        assert_eq!(stype.rs2, Register::Zero);
        assert_eq!(stype.rs1, Register::T0);
        assert_eq!(stype.imm11_0, 0);
    }

    #[test]
    fn stype_sw_ra_12_sp() {
        // 23 26 11 00  	sw	ra, 12(sp)
        // imm11:5 rs2 rs1 010 imm4:0 0100011
        let instruction =
            u32::from_le_bytes([0x23, 0x26, 0x11, 0x00]);

        let stype = Stype::from(instruction);

        assert_eq!(stype.funct3, 0b010);
        assert_eq!(stype.rs2, Register::Ra);
        assert_eq!(stype.rs1, Register::Sp);
        assert_eq!(stype.imm11_0, 12);
    }

    #[test]
    fn stype_sw_a0_m788_a5() {
        // 23 a6 a7 ce  	sw	a0, -788(a5)
        // imm11:5 rs2 rs1 010 imm4:0 0100011
        let instruction =
        u32::from_le_bytes([0x23, 0xa6, 0xa7, 0xce]);

        let stype = Stype::from(instruction);

        assert_eq!(stype.funct3, 0b010);
        assert_eq!(stype.rs2, Register::A0);
        assert_eq!(stype.rs1, Register::A5);
        assert_eq!(stype.imm11_0, -788i32 as u32);
    }

    #[test]
    fn stype_sh_a5_m772_s1() {
        // 23 9e f4 ce  	sh	a5, -772(s1)
        // imm11:5 rs2 rs1 001 imm4:0 0100011
        let instruction =
            u32::from_le_bytes([0x23, 0x9e, 0xf4, 0xce]);

        let stype = Stype::from(instruction);

        assert_eq!(stype.funct3, 0b001);
        assert_eq!(stype.rs2, Register::A5);
        assert_eq!(stype.rs1, Register::S1);
        assert_eq!(stype.imm11_0, -772i32 as u32);
    }

    #[test]
    fn stype_sb_a5_m1_s0() {
        // a3 0f f4 fe  	sb	a5, -1(s0)
        // imm11:5 rs2 rs1 000 imm4:0 0100011
        let instruction =
            u32::from_le_bytes([0xa3, 0x0f, 0xf4, 0xfe]);

        let stype = Stype::from(instruction);

        assert_eq!(stype.funct3, 0b000);
        assert_eq!(stype.rs2, Register::A5);
        assert_eq!(stype.rs1, Register::S0Fp);
        assert_eq!(stype.imm11_0, -1i32 as u32);
    }

    #[test]
    fn utype_lui_a5_7933() {
        // b7 d7 ef 01  	lui	a5, 7933
        // imm31:12 rd 0110111
        let instruction =
            u32::from_le_bytes([0xb7, 0xd7, 0xef, 0x01]);

        let utype = Utype::from(instruction);

        assert_eq!(utype.rd, Register::A5);
        assert_eq!(utype.imm31_12, 7933);
    }

    #[test]
    fn utype_auipc_t1_1() {
        // 17 13 00 00  	auipc	t1, 1
        // imm31:12 rd 0010111
        let instruction =
            u32::from_le_bytes([0x17, 0x13, 0x00, 0x00]);

        let utype = Utype::from(instruction);

        assert_eq!(utype.rd, Register::T1);
        assert_eq!(utype.imm31_12, 1);
    }


    #[test]
    fn jtype_j_0x258() {
        // pseudo-instruction "j offset" = "jal x0/Zero offset"
        // 2000: 6f 00 80 25  	j	0x2258 <start>
        //       imm20 10_1 11 19_12  (X0/Zero)  1101111
        let instruction =
            u32::from_le_bytes([0x6f, 0x00, 0x80, 0x25]);

        let jtype = Jtype::from(instruction);

        assert_eq!(jtype.rd, Register::Zero);
        // the original instruction was at address 0x2000
        assert_eq!(jtype.offset, 0x258i32);
    }

    #[test]
    fn jtype_j_m0x2c() {
        // pseudo-instruction "j offset" = "jal x0/Zero offset"
        // 239c: 6f f0 5f fd  	j	0x2370
        //       imm20 10_1 11 19_12  (X0/Zero)  1101111
        let instruction =
            u32::from_le_bytes([0x6f, 0xf0, 0x5f, 0xfd]);

        let jtype = Jtype::from(instruction);

        assert_eq!(jtype.rd, Register::Zero);
        // the original instruction was at address 0x239c
        assert_eq!(jtype.offset, -0x2c);
    }

}
