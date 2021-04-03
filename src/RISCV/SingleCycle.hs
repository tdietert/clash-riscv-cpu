{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module RISCV.SingleCycle (topEntity) where

import Clash.Prelude
import Clash.Debug

----------------------------------------
-- Top Entity
----------------------------------------

testProgram :: Vec 7 Insn
testProgram =
     AddI 0x1 0x0 0x5 -- [0] counter = 5
  :> AddI 0x2 0x0 0x8 -- [4] end = 8
  :> AddI 0x3 0x0 0x1 -- [8] sum = 0
  :> BranchIfEq 0x1 0x2 0x8 -- [12] if counter == end, jmp
  :> Add 0x3 0x3 0x1 -- [16] sum = sum + counter
  :> AddI 0x1 0x1 0x1 -- [20] counter = counter + 1
  :> BranchIfEq 0x0 0x0 (-0x6) -- [24]
  :> Nil -- [28]

testProgram2 :: Vec 1 Insn
testProgram2 =
     Add 0x1 0x1 0x1
  :> Nil

----------------------------------------

-- | 'topEntity' is Clash's equivalent of 'main' in other programming
-- languages. Clash will look for it when compiling 'Example.Project'
-- and translate it to HDL. While polymorphism can be used freely in
-- Clash projects, a 'topEntity' must be monomorphic and must use non-
-- recursive types. Or, to put it hand-wavily, a 'topEntity' must be
-- translatable to a static number of wires.
topEntity :: Signal System (CpuOut, CpuIn)
topEntity =
  case loadInsnMem testProgram of
    Nothing -> errorX "Failed to initialize Instruction memory"
    Just insnMem -> system @System insnMem

----------------------------------------
-- Abstract types of RV32I instruction bitfields
----------------------------------------

newtype ReadReg1 = ReadReg1 (BitVector 5)
  deriving stock (Show, Generic)
  deriving newtype (Enum, Num, ShowX, NFDataX)
  deriving anyclass (BitPack)

newtype ReadReg2 = ReadReg2 (BitVector 5)
  deriving stock (Show, Generic)
  deriving newtype (Enum, Num, ShowX, NFDataX)
  deriving anyclass (BitPack)

newtype WriteReg = WriteReg (BitVector 5)
  deriving stock (Show, Generic)
  deriving newtype (Enum, Num, ShowX, NFDataX)
  deriving anyclass (BitPack)

newtype OpCode   = OpCode (BitVector 7)
  deriving stock (Show, Generic)
  deriving newtype (Enum, Num, ShowX, NFDataX)
  deriving anyclass (BitPack)

----------------------------------------
-- Instructions
----------------------------------------

type InsnImm = BitVector 12

data InsnType
  = RType
  | IType
  | SType
  | SBType
  -- UType
  -- UJType

data Insn
  = Load       { lw_rd   :: !WriteReg, lw_rs1   :: !ReadReg1, lw_imm   :: !InsnImm }
  | Store      { sw_rs1  :: !ReadReg1, sw_rs2   :: !ReadReg2, sw_imm   :: !InsnImm }
  | Add        { add_rd  :: !WriteReg, add_rs1  :: !ReadReg1, add_rs2  :: !ReadReg2 }
  | AddI       { addi_rd :: !WriteReg, addi_rs1 :: !ReadReg1, addi_imm :: !InsnImm }
  | Sub        { sub_rd  :: !WriteReg, sub_rs1  :: !ReadReg1, sub_rs2  :: !ReadReg2 }
  | And        { and_rd  :: !WriteReg, and_rs1  :: !ReadReg1, and_rs2  :: !ReadReg2 }
  | Or         { or_rd   :: !WriteReg, or_rs1   :: !ReadReg1, or_rs2   :: !ReadReg2 }
  | BranchIfEq { beq_rs1 :: !ReadReg1, beq_rs2  :: !ReadReg2, beq_imm  :: !InsnImm }
  deriving (Show)

-- | An instruction's decoded bit fields
data InsnBitFields
  = InsnBitFields
  { opCode   :: !OpCode      -- ^ Bits [6:0]
  , writeReg :: !WriteReg    -- ^ Bits [11:7]
  , funct3   :: !(BitVector 3) -- ^ Bits [14:12]
  , readReg1 :: !ReadReg1    -- ^ Bits [19:15]
  , readReg2 :: !ReadReg2    -- ^ Bits [24:20]
  , funct7   :: !(BitVector 7) -- ^ Bits [31:25]
  } deriving (Show, Generic, ShowX, NFDataX)

-- | By pattern matching on Insn, we can use InsnBitFields to reconstruct
-- the instruction's binary representation.
-- encodeInsnBitFields :: InsnBitFields -> RawInsn
-- encodeInsnBitFields (InsnBitFields opcode rd f3 rs1 rs2 f7 ) =
--   unpack (f7 ++# pack rs2 ++# pack rs1 ++# f3 ++# pack rd ++# pack opcode)

encodeInsn :: Insn -> RawInsn
encodeInsn insn =
    unpack (bits31to25 ++# bits24to20 ++# bits19to15 ++# bits14to12 ++# bits11to7 ++# opcode)
  where
    opcode = insnOpCode insn
    bits11to7 = insnBits11to7 insn
    bits14to12 = insnFunct3 insn
    bits19to15 = insnBits19to15 insn
    bits24to20 = insnBits24to20 insn
    bits31to25 = insnFunct7 insn

insnOpCode :: Insn -> BitVector 7
insnOpCode (Load _ _ _) = 0b0110011
insnOpCode (Store _ _ _) = 0b0100011
insnOpCode (Add _ _ _) = 0b0110011
insnOpCode (AddI _ _ _) = 0b0010011
insnOpCode (Sub _ _ _) = 0b0110011
insnOpCode (And _ _ _) = 0b0110011
insnOpCode (Or _ _ _) = 0b0110011
insnOpCode (BranchIfEq _ _ _) = 0b1100011

insnBits11to7 :: Insn -> BitVector 5
insnBits11to7 (Load rd _ _) = pack rd
insnBits11to7 (Store _ _ imm) = slice d4 d0 imm
insnBits11to7 (Add rd _ _) = pack rd
insnBits11to7 (AddI rd _ _) = pack rd
insnBits11to7 (Sub rd _ _) = pack rd
insnBits11to7 (And rd _ _) = pack rd
insnBits11to7 (Or rd _ _) = pack rd
insnBits11to7 (BranchIfEq _ _ imm) = slice d3 d0 imm ++# pack (imm ! 10)

insnFunct3 :: Insn -> BitVector 3
insnFunct3 (Load _ _ _) = 0b010
insnFunct3 (Store _ _ _) = 0b010
insnFunct3 (Add _ _ _) = 0b000
insnFunct3 (AddI _ _ _) = 0b000
insnFunct3 (Sub _ _ _) = 0b000
insnFunct3 (And _ _ _) = 0b111
insnFunct3 (Or _ _ _) = 0b110
insnFunct3 (BranchIfEq _ _ _) = 0b000

insnBits19to15 :: Insn -> BitVector 5
insnBits19to15 (Load _ rs1 _) = pack rs1
insnBits19to15 (Store rs1 _ _) = pack rs1
insnBits19to15 (Add _ rs1 _) = pack rs1
insnBits19to15 (AddI _ rs1 _) = pack rs1
insnBits19to15 (Sub _ rs1 _) = pack rs1
insnBits19to15 (And _ rs1 _) = pack rs1
insnBits19to15 (Or _ rs1 _) = pack rs1
insnBits19to15 (BranchIfEq rs1 _ _) = pack rs1

insnBits24to20 :: Insn -> BitVector 5
insnBits24to20 (Load _ _ imm) = slice d4 d0 imm
insnBits24to20 (Store _ rs2 _) = pack rs2
insnBits24to20 (Add _ _ rs2) = pack rs2
insnBits24to20 (AddI _ _ imm) = slice d4 d0 imm
insnBits24to20 (Sub _ _ rs2) = pack rs2
insnBits24to20 (And _ _ rs2) = pack rs2
insnBits24to20 (Or _ _ rs2) = pack rs2
insnBits24to20 (BranchIfEq _ rs2 _) = pack rs2

insnFunct7 :: Insn -> BitVector 7
insnFunct7 (Load _ _ imm) = slice d11 d5 imm
insnFunct7 (Store _ _ imm) = slice d11 d5 imm
insnFunct7 (Add _ _ _) = 0b0000000
insnFunct7 (AddI _ _ imm) = slice d11 d5 imm
insnFunct7 (Sub _ _ _) = 0b0100000
insnFunct7 (And _ _ _) = 0b0000000
insnFunct7 (Or _ _ _) = 0b0000000
insnFunct7 (BranchIfEq _ _ imm) =
  let imm12 = pack (imm ! 11)
      imm10to5 = slice d9 d4 imm
  in imm12 ++# imm10to5

decodeInsn :: RawInsn -> (Insn, InsnBitFields)
decodeInsn insnBits = (insn, insnFields)
  where
    -- Figure out which instruction it is here to simplify logic further down
    -- the datapath
    insn =
      case opcodeBits of
        0b0110011 -> -- Add/Sub/And/Or
          case funct3Bits of
            0b000 -> -- Add/Sub
              case funct7Bits of
                0b0000000 -> Add wrReg rdReg1 rdReg2
                0b0100000 -> Sub wrReg rdReg1 rdReg2
                _ -> errorX "Instruction decode error: Add/Sub"
            0b111 -> And wrReg rdReg1 rdReg2
            0b110 -> Or wrReg rdReg1 rdReg2
            _ -> errorX "Instruction decode error: R-Type"
        0b0010011 -> -- AddI
          case funct3Bits of
            0b000 ->
              let addiImm = funct7Bits ++# rs2Bits
              in AddI wrReg rdReg1 addiImm
            _ -> errorX "Instruction decode error: I-Type"
        0b0000011 -> -- Load
          -- Note: funct3 differs based on type of "load" (e.g. 32/64b)
          case funct3Bits of
            0b010 ->
              let lwImm = funct7Bits ++# rs2Bits
              in Load wrReg rdReg1 lwImm
            _ -> errorX "Instruction decode error: I-Type"
        0b0100011 -> -- Store
          -- Note: funct3 differs based on type of "store" (e.g. 32/64b)
          case funct3Bits of
            0b010 ->
              let swImm = funct7Bits ++# rdBits
              in Store rdReg1 rdReg2 swImm -- sw
            _ -> errorX "Instruction decode error: S-Type"
        0b1100011 -> -- Branch-If-Eq
          case funct3Bits of
            0b000 ->
              -- TODO Extract immediate construction into function
              let imm12 = pack (funct7Bits ! 6)
                  imm11 = pack (rdBits ! 0)
                  imm10to5 = slice d5 d0 funct7Bits
                  imm4to1 = slice d4 d1 rdBits
                  beqImm = imm12 ++# imm11 ++# imm10to5 ++# imm4to1
              in BranchIfEq rdReg1 rdReg2 beqImm
            _ -> errorX "Instruction decode error: SB-Type"
        _ -> errorX "Instruction decode error: Invalid op code"

    opcodeBits = slice d6 d0 insnBits
    rdBits     = slice d11 d7 insnBits
    funct3Bits = slice d14 d12 insnBits
    rs1Bits    = slice d19 d15 insnBits
    rs2Bits    = slice d24 d20 insnBits
    funct7Bits = slice d31 d25 insnBits

    opcode = OpCode opcodeBits
    wrReg = WriteReg rdBits
    rdReg1 = ReadReg1 rs1Bits
    rdReg2 = ReadReg2 rs2Bits

    insnFields = InsnBitFields
      { opCode = opcode
      , writeReg = wrReg
      , funct3 = funct3Bits
      , readReg1 = rdReg1
      , readReg2 = rdReg2
      , funct7 = funct7Bits
      }


----------------------------------------
-- Control Unit
----------------------------------------

data CtrlLines
  = CtrlLines
  { branch :: Bit
  , memRead :: Bit
  , memToReg :: Bit
  --, aluOp :: Unsigned 2
  , memWrite :: Bit
  , aluSrc :: Bit
  , regWrite :: Bit
  }

control :: OpCode -> CtrlLines
control (OpCode opcode) =
  case opcode of
    0b0110011 -> -- R-Type instruction
      CtrlLines
      { branch = 0b0
      , memRead = 0b0
      , memToReg = 0b0
      --, aluOp = 0b10
      , memWrite = 0b0
      , aluSrc = 0b0
      , regWrite = 0b1
      }
    0b0000011 -> -- Load Instruction
      CtrlLines
      { branch = 0b0
      , memRead = 0b1
      , memToReg = 0b1
      --, aluOp = 0b00
      , memWrite = 0b0
      , aluSrc = 0b1
      , regWrite = 0b1
      }
    0b0010011 -> -- AddI Instruction
      CtrlLines
      { branch = 0b0
      , memRead = 0b0
      , memToReg = 0b0
      --, aluOp = 0b00
      , memWrite = 0b0
      , aluSrc = 0b1
      , regWrite = 0b1
      }
    0b0100011 -> -- S-Type Instruction
      CtrlLines
      { branch = 0b0
      , memRead = 0b1
      , memToReg = 0b0
      --, aluOp = 0b00
      , memWrite = 0b1
      , aluSrc = 0b1
      , regWrite = 0b0
      }
    0b1100011 -> -- B-Type Instruction
      CtrlLines
      { branch = 0b1
      , memRead = 0b0
      , memToReg = 0b0
      --, aluOp = 0b01
      , memWrite = 0b0
      , aluSrc = 0b0
      , regWrite = 0b0
      }
    _ -> errorX $ mconcat
      [ "Invalid bit pattern to control unit... ", show opcode ]

----------------------------------------
-- Register File
----------------------------------------

-- The type of values that inhabit the CPU datapath
type Data = Signed 32

type Registers = Vec 32 Data

initRegisters :: Registers
initRegisters = replicate d32 0x0

-- | Combinational register file with two read ports and one write port
--
-- The register can be written to and read in the same clock cycle, and a read
-- will always follow a potential register write.
registerFile
  :: Registers
  -> (ReadReg1, ReadReg2, Maybe (WriteReg, Data))
  -> (Registers, (Data, Data))
registerFile regs (rdReg1, rdReg2, mWrReg) =
  case mWrReg of
    Just (wrReg, wrData) ->
      let wrRegs = replace 0x0 0x0 (replace wrReg wrData regs)
      in (wrRegs, (wrRegs !! rdReg1, wrRegs !! rdReg2))
    Nothing -> (regs, (regs !! rdReg1, regs !! rdReg2))

----------------------------------------
-- ALU
----------------------------------------

-- | ALU unit
alu :: Insn -> Data -> Data -> (Data, Bool)
alu insn a b = (aluOut, aluZero)
  where
    -- No need to generate ALUOp signals from the Control unit as we can just reuse
    -- the Insn value from the instruction decoder
    --
    -- TODO make function `aluCtrl :: Insn -> AluOp`
    aluOut :: Data
    aluOut =
      case insn of
        And _ _ _ -> a .&. b
        Or _ _ _ ->  a .|. b
        Load _ _ _ -> a + b
        Store _ _ _ -> a + b
        Add _ _ _ -> a + b
        AddI _ _ _ -> a + b
        Sub _ _ _ -> a - b
        BranchIfEq _ _ _ -> a - b

    aluZero = aluOut == 0

----------------------------------------
-- Immediate Generation
----------------------------------------

-- | In the case of "data transfer" isnstructions (Load + Store), opcode bit [6]
-- = 0, but for conditional branches bit [6] = 1. In the case of 'store' opcode
-- bit [5] = 1, whereas for 'load' bit [5] = 0 Thus, a 3:1 mux can select the
-- appropriate bit fields comprising the immediate value (see above).
--
-- Bit fields comprising the immediate to sign extend depend on the instruction:
-- - Load: [31:20]
-- - Store: [31:25]+[11:7]
-- - Cond-Branch: [31]+[7]+[30:25]+[11:8]
-- - R-Type: None...
--
-- After extracting the proper bit fields comprising the 12 bit immediate value,
-- shift the result 12 bit value left by 1 for a half-word offset. The RISC-V
-- ISA spec requires byte-addressable memory, and shifting the immediate value
-- left by one increases the effective range of the offsets of instructions with
-- base or PC-relative addressing schemes while limiting the precision of the
-- address to every half-word. *This left bit shift happens in the CPU
-- datapath*.
immGen
  :: InsnBitFields
  -> Maybe Data
immGen ibfs = signExtend . unpack <$> imm
  where
    OpCode opcode = opCode ibfs
    ReadReg2 rdReg2 = readReg2 ibfs
    WriteReg wrReg = writeReg ibfs
    f7 = funct7 ibfs

    imm :: Maybe (BitVector 12)
    imm =
      case slice d6 d5 opcode of
        $(bitPattern "00") -> Just (f7 ++# rdReg2) -- Load/AddI Insn / I-Type
        $(bitPattern "01") -> Just (f7 ++# wrReg) -- Store Insn / R-Type
        $(bitPattern "11") -> -- BranchIfEq Insn (most complicated, SB-Type)
          let imm12_10to5 = f7
              imm4to1_11 = wrReg
          in Just $ pack (imm12_10to5 ! 6)
                ++# pack (imm4to1_11 ! 0)
                ++# slice d5 d0 imm12_10to5
                ++# slice d4 d1 imm4to1_11
        _ -> Nothing

----------------------------------------
-- Memory
--
-- TODO Equate InsnMem and InsnAddr sizes
-- TODO Equate DataMem and DataAddr sizes
----------------------------------------

type RawInsn = BitVector 32
type InsnAddr = Unsigned 8
-- For Instruction Memory 2^8'
type InsnMemSize = 256

insnMemSize :: SNat InsnMemSize
insnMemSize = SNat

type InsnMem = Vec InsnMemSize RawInsn

-- | Create an instruction memory from a vector of instructions
loadInsnMem
  :: forall n m.
     (KnownNat n, KnownNat m, n <= InsnMemSize, m ~ (InsnMemSize - n))
  => Vec n Insn
  -> Maybe InsnMem
loadInsnMem = loadInsnMemRaw . map encodeInsn

loadInsnMemRaw
  :: forall n m.
     (KnownNat n, KnownNat m, n <= InsnMemSize, m ~ (InsnMemSize - n))
  => Vec n RawInsn
  -> Maybe InsnMem
loadInsnMemRaw insns =
  case lengthS insns of
    snat@SNat ->
      case subSNat insnMemSize snat of
        sizeDiff@(SNat :: SNat m) -> Just (insns ++ replicate sizeDiff 0x0)

readInsnMem
  :: InsnMem
  -> InsnAddr
  -> RawInsn
readInsnMem insnMem = asyncRom insnMem . flip div 4

type DataAddr = Unsigned 8
type DataMemSize = 256

-- | Synchronous data memory
dataMem
  :: HiddenClockResetEnable dom
  => Signal dom DataAddr
  -> Signal dom (Maybe (DataAddr, Data))
  -> Signal dom Data
dataMem = blockRam (replicate (SNat :: SNat DataMemSize) 0x0)

----------------------------------------
-- CPU
----------------------------------------

newtype PC = PC InsnAddr
  deriving stock (Show, Generic)
  deriving newtype (Enum, Num)
  deriving anyclass (ShowX, BitPack, NFDataX)

data CpuState
  = CpuState
  { currPC :: PC
  , regFile :: Registers
  } deriving (Generic, NFDataX)

initCpuState :: CpuState
initCpuState = CpuState (PC 0) initRegisters

-- | Potential data and write register from previous cycle
type CpuIn = Maybe (WriteReg, Data)

type CpuOut =
  ( DataAddr -- DataMem Read addr
  , Data -- ALU Out
  , Maybe (DataAddr, Data) -- DataMem Write addr and data
  , Maybe (WriteReg, Maybe Data) -- WriteReg Data
  , PC -- Program Counter
  )

-- | Single cycle central processing unit transition function
cpu
  :: HiddenClockResetEnable dom
  => InsnMem
  -> CpuState
  -> CpuIn
  -> (CpuState, CpuOut)
cpu insnMem (CpuState pc@(PC insnAddr) regs) ~mWrData =
    (cpuState, cpuOut)
  where
    -- Instruction Fetch
    insnRaw = readInsnMem insnMem insnAddr

    -- Instruction Decode
    (insn, ibfs) = decodeInsn insnRaw
    rdReg1 = readReg1 ibfs
    rdReg2 = readReg2 ibfs
    wrReg = writeReg ibfs

    -- Immediate Generation
    mImmGenOut = immGen ibfs

    -- Compute control lines
    ctrlLines = control (opCode ibfs)
    ctrlMemToReg = memToReg ctrlLines
    ctrlMemWrite = memWrite ctrlLines
    ctrlRegWrite = regWrite ctrlLines
    ctrlBranch = branch ctrlLines
    ctrlAluSrc = aluSrc ctrlLines

    -- Read registers based on decoded instruction
    (nextRegFile, (readData1, readData2)) =
      registerFile regs (rdReg1, rdReg2, mWrData)

    -- Compute result from ALU
    aluIn
      | bitToBool ctrlAluSrc =
          case mImmGenOut of
            Nothing -> errorX "ImmGen should not have Nothing result"
            Just immGenOut -> immGenOut
      | otherwise = readData2
    (aluOut, aluZero) =
      alu insn readData1 aluIn

    aluAddr :: DataAddr
    aluAddr = bitCoerce . resize $ aluOut

    -- PC calculation
    -- TODO Byte Addressing (Currently insnMem divides PC by 4)
    incrPC = pc + 4
    nextPC = case mImmGenOut of
      Nothing -> incrPC
      Just immGenOut
        | aluZero && bitToBool ctrlBranch ->
            let immGenSext = resize (shiftL immGenOut 1)
             -- We must treat insnAddr as signed in this case, then convert the
             -- result back to unsigned.
             in PC (bitCoerce (bitCoerce insnAddr + immGenSext))
        | otherwise -> incrPC

    -- CpuOut value calculation
    readDataMem = aluAddr
    writeDataMem
      | bitToBool ctrlMemWrite = Just (aluAddr, readData2)
      | otherwise = Nothing
    writeRegFile
      | bitToBool ctrlRegWrite =
          if bitToBool ctrlMemToReg
            then Just (wrReg, Nothing)
            else Just (wrReg, Just aluOut)
      | otherwise = Nothing

    cpuOut = (readDataMem, aluOut, writeDataMem, writeRegFile, pc)

    cpuState =
      CpuState
      { currPC = nextPC
      , regFile = nextRegFile
      }

----------------------------------------
-- System
----------------------------------------

system
  :: HiddenClockResetEnable dom
  => InsnMem
  -> Signal dom (CpuOut, CpuIn)
system insnMem = bundle (bundle cpuOut, cpuIn)
  where
    ~cpuOut@(readDataMem, aluOut, writeDataMem, ~writeRegFile, pc) =
      mealyB (cpu insnMem) initCpuState cpuIn

    dataMemOut = dataMem readDataMem writeDataMem

    ~cpuIn = register Nothing (liftA2 cpuInCtrl writeRegFile dataMemOut)

    -- If the 'writeReg' control signal is low
    --   then: don't write to the register file
    --   else:
    --     If 'memToReg' is high
    --       then: return the data read from DataMem
    --       else: return the data computed from the ALU
    --
    -- * Nothing = No write to register file
    -- * Just (wrReg, Nothing) = Write result of data mem to the write register
    -- * Just (wrReg, Just aluOut) = Write alu out data to the write register
    cpuInCtrl :: Maybe (WriteReg, Maybe Data) -> Data -> Maybe (WriteReg, Data)
    cpuInCtrl meWrReg readMemData =
      case meWrReg of
        Nothing -> Nothing
        Just (wrReg, Nothing) -> Just (wrReg, readMemData)
        Just (wrReg, Just aluOutData) -> Just (wrReg, aluOutData)
