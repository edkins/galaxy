module X86 where

import Data.Bits ((.&.),(.|.),shiftL,shiftR)
import Data.ByteString.Builder
import Data.Monoid ((<>))
import Data.Word (Word8,Word16,Word32,Word64)

data Code = Code Builder Int

data Reg = Xmm Word8 | Gpr Word8 deriving Eq
data RM = R Reg | AbsMem Int | NoRM
data Opcode = I_66_0F Word8 | I_66_0F38 Word8
data OpcodeO = Old_OI Int Word8

instance Monoid Code where
    mempty = Code mempty 0
    mappend (Code b0 l0) (Code b1 l1) = Code (b0 <> b1) (l0 + l1)

------------------
movdqa_rm = I_66_0F 0x6f
mov_oi8 = Old_OI 1 0xb0 -- 0xb0 thru 0xb7
vpbroadcastb_rm = I_66_0F38 0x78
paddb_rm = I_66_0F 0xfc

------------------
b :: Word8 -> Code
b w = Code (word8 w) 1

wd :: Word16 -> Code
wd w = Code (word16LE w) 2

dw :: Word32 -> Code
dw w = Code (word32LE w) 4

qw :: Word64 -> Code
qw w = Code (word64LE w) 8

bytes :: [Word8] -> Code
bytes [] = mempty
bytes (x:xs) = b x <> bytes xs

clength :: Code -> Int
clength (Code _ l) = l

zeros :: Int -> Code
zeros n = bytes (replicate n 0)

code_as_builder :: Code -> Builder
code_as_builder (Code b _) = b

-------------------
sse_rm :: Opcode -> Reg -> RM -> Code
sse_rm (I_66_0F op) r rm = b 0x66 <> maybe_rex r rm 0 <> b 0x0f <> b op <> modrm_sib_disp r rm

old_oi :: OpcodeO -> Reg -> Int -> Code
old_oi (Old_OI imsize op) (Gpr reg) imval =
    let
        mrex = maybe_rex (Gpr reg) NoRM 0
        r = reg .&. 7
        op' = op + r
        imm = int_as_n_bytes imsize imval
    in
        mrex <> b op' <> imm

vex128_rm :: Opcode -> Reg -> RM -> Code
vex128_rm (I_66_0F38 op) r rm =
    let
        vx = vex r rm 0 2 0 1    --vex reg rm w' m_mmmm l pp
    in
        vx <> b op <> modrm_sib_disp r rm

------------------
get_r :: Reg -> Word8
get_r (Xmm reg) = reg .&. 7
get_r (Gpr reg) = reg .&. 7

modrm_sib_disp :: Reg -> RM -> Code
modrm_sib_disp reg (AbsMem addr) =
    let
        r = get_r reg
        mod = 0
        rm = 4
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
        disp = int_as_four_bytes addr
    in
        b modrm <> disp
modrm_sib_disp reg (R reg') =
    let
        r = get_r reg
        rm = get_r reg'
        mod = 3
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
    in
        b modrm

rex_r :: Reg -> Word8
rex_r (Xmm n) = (n .&. 8) `shiftR` 3
rex_r (Gpr n) = (n .&. 8) `shiftR` 3

rex_x :: RM -> Word8
rex_x (R _) = 0
rex_x (AbsMem _) = 0
rex_x NoRM = 0

rex_b :: RM -> Word8
rex_b (R (Xmm n)) = (n .&. 8) `shiftR` 3
rex_b (R (Gpr n)) = (n .&. 8) `shiftR` 3
rex_b (AbsMem _) = 0
rex_b NoRM = 0

maybe_rex :: Reg -> RM -> Word8 -> Code
maybe_rex reg rm w =
    let
        r = rex_r reg
        x = rex_x rm
        b' = rex_b rm
        rex = 0x40 .|. (w `shiftL` 3) .|. (r `shiftL` 2) .|. (x `shiftL` 1) .|. b'
    in
        if rex == 0x40 then
            mempty
        else
            b rex

vex :: Reg -> RM -> Word8 -> Word8 -> Word8 -> Word8 -> Code
vex reg rm w' m_mmmm l pp =
    let
        r = 1 - rex_r reg
        w = 1 - w'
        x = 1 - rex_x rm
        b' = 1 - rex_b rm
        vvvv = 15
    in
        if m_mmmm == 1 && w == 1 && x == 1 && b' == 1 then
            -- two-byte vex
            b 0xc5 <>
                b ((r `shiftL` 7) .|. (vvvv `shiftL` 3) .|. (l `shiftL` 2) .|. pp)
        else
            -- three-byte vex
            b 0xc4 <>
                b ((r `shiftL` 7) .|. (x `shiftL` 6) .|. (b' `shiftL` 5) .|. m_mmmm) <>
                b ((w `shiftL` 7) .|. (vvvv `shiftL` 3) .|. (l `shiftL` 2) .|. pp)

xmm_addr :: Reg -> Word8
xmm_addr (Xmm n) = n

int_as_n_bytes :: Int -> Int -> Code
int_as_n_bytes 0 0 = mempty
int_as_n_bytes 0 int = error ("int_as_n_bytes: " ++ show int ++ " left over")
int_as_n_bytes n int = b (fromIntegral (int .&. 0xff)) <> int_as_n_bytes (n-1) (int `shiftR` 8)

int_as_four_bytes :: Int -> Code
int_as_four_bytes int = int_as_n_bytes 4 int

