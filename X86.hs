module X86 where

import Data.Bits ((.&.),(.|.),shiftL,shiftR)
import Data.ByteString.Builder
import Data.Monoid ((<>))
import Data.Word (Word8,Word16,Word32,Word64)

data Code = Code Builder Int

data Reg = Xmm Word8 | Gpr Word8 | NoReg | Slash Word8 deriving (Eq,Show)
data RM = R Reg | AbsMem Int | RegMem Reg Int | SibMem Int Reg Reg Int | NoRM deriving Eq
data Opcode = I_0F Word8 | I_66_0F Word8 | I_F3_0F Word8 | I_66_0F38 Word8 | I_66_0F_slash Word8 Word8
data OpcodeO = Old_OI Word8 Int Word8 | Old_MI_slash Word8 Int Word8 Word8 | Old_RM Word8 Word8
    | Old_I Word8 Int Word8 | Old_ZO Word8 Word8

instance Monoid Code where
    mempty = Code mempty 0
    mappend (Code b0 l0) (Code b1 l1) = Code (b0 <> b1) (l0 + l1)

------------------
add_mi8_slash = Old_MI_slash 1 1 0x83 0  -- REX.W 0x83/0, 1-byte immediate
call_i32 = Old_I 1 4 0xe8 -- 0xe8, 4-byte relative address
mov_oi8 = Old_OI 0 1 0xb0 -- 0xb0 thru 0xb7, 1-byte immediate
mov_oi64 = Old_OI 1 8 0xb8 -- REX.W 0xb8 thru 0xbf, 8-byte immediate
mov_rm = Old_RM 1 0x8b   -- REX.W 0x8b, modrm
ret_zo = Old_ZO 0 0xc3
sub_mi8_slash = Old_MI_slash 1 1 0x83 5  -- REX.W 0x83/5, 1-byte immediate
syscall_zo = I_0F 0x05
vpaddb_rrm = I_66_0F 0xfc
vpand_rrm = I_66_0F 0xdb
vpbroadcastb_rm = I_66_0F38 0x78
vpcmpgtb_rrm = I_66_0F 0x64
vmovdqa_mr = I_66_0F 0x7f
vmovdqa_rm = I_66_0F 0x6f
vmovdqu_mr = I_F3_0F 0x7f
vpmovzxbw_rm = I_66_0F38 0x30
vpor_rrm = I_66_0F 0xeb
vpsllw_rmi_slash = I_66_0F_slash 0x71 6
vpsrlw_rmi_slash = I_66_0F_slash 0x71 2

-- evex instructions
evpbroadcastb_gpr_rm = I_66_0F38 0x7a


------------------
_ax = Gpr 0
_cx = Gpr 1
_dx = Gpr 2
_bx = Gpr 3
_sp = Gpr 4
_bp = Gpr 5
_si = Gpr 6
_di = Gpr 7
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

strbytes :: String -> Code
strbytes str = Code (string7 str) (length str)

clength :: Code -> Int
clength (Code _ l) = l

zeros :: Int -> Code
zeros n = bytes (replicate n 0)

code_as_builder :: Code -> Builder
code_as_builder (Code b _) = b

-------------------
sse_rm :: Opcode -> Reg -> RM -> Code
sse_rm (I_66_0F op) r rm = b 0x66 <> maybe_rex r rm 0 <> b 0x0f <> b op <> modrm_sib_disp r rm

sse_zo (I_0F op) = b 0x0f <> b op

old_i :: OpcodeO -> Int -> Code
old_i (Old_I w imsize op) imval =
    let
        mrex = maybe_rex NoReg NoRM w
        imm = int_as_n_bytes imsize imval
    in
        mrex <> b op <> imm

old_oi :: OpcodeO -> Reg -> Int -> Code
old_oi (Old_OI w imsize op) (Gpr reg) imval =
    let
        mrex = maybe_rex (Gpr reg) NoRM w
        r = reg .&. 7
        op' = op + r
        imm = int_as_n_bytes imsize imval
    in
        mrex <> b op' <> imm

old_mi_slash :: OpcodeO -> RM -> Int -> Code
old_mi_slash (Old_MI_slash w imsize op slash) rm imval =
    let
        mrex = maybe_rex (Slash slash) rm w
        imm = int_as_n_bytes imsize imval
    in
        mrex <> b op <> modrm_sib_disp (Slash slash) rm <> imm

old_rm :: OpcodeO -> Reg -> RM -> Code
old_rm (Old_RM w op) (Gpr reg) rm =
    let
        mrex = maybe_rex (Gpr reg) NoRM w
    in
        mrex <> b op <> modrm_sib_disp (Gpr reg) rm

old_zo :: OpcodeO -> Code
old_zo (Old_ZO w op) =
    let
        mrex = maybe_rex NoReg NoRM w
    in
        mrex <> b op

old_misc :: Word8 -> Word8 -> Word8 -> Word8 -> Reg -> RM -> Code -> Code
old_misc w pp mmmmm op (Gpr reg) rm imm =
    let
        mrex = maybe_rex (Gpr reg) rm w
    in
        old_pp pp <> mrex <> old_mmmmm mmmmm <> b op <> modrm_sib_disp (Gpr reg) rm <> imm
old_misc w pp mmmmm op (Slash n) rm imm =
    let
        mrex = maybe_rex (Slash n) rm w
    in
        old_pp pp <> mrex <> old_mmmmm mmmmm <> b op <> modrm_sib_disp (Slash n) rm <> imm

old_misc_no_modrm :: Word8 -> Word8 -> Word8 -> Word8 -> Code -> Code
old_misc_no_modrm w pp mmmmm op imm =
    let
        mrex = maybe_rex NoReg NoRM w
    in
        old_pp pp <> mrex <> old_mmmmm mmmmm <> b op <> imm

old_pp :: Word8 -> Code
old_pp 0 = mempty
old_pp 1 = bytes [0x66]
old_pp 2 = bytes [0xf3]
old_pp 3 = bytes [0xf2]

old_mmmmm :: Word8 -> Code
old_mmmmm 0 = mempty
old_mmmmm 1 = bytes [0x0f]
old_mmmmm 2 = bytes [0x0f,0x38]
old_mmmmm 3 = bytes [0x0f,0x3a]

------------------------

vex128_rm :: Opcode -> Reg -> RM -> Code
vex128_rm op r rm = vex_rrm op 0 0 r NoReg rm mempty

vex128_rmi_slash :: Opcode -> Reg -> RM -> Word8 -> Code
vex128_rmi_slash op rv rm imval = vex_rrm op 0 0 (get_slash op) rv rm (b imval)

vex128_rrm :: Opcode -> Reg -> Reg -> RM -> Code
vex128_rrm op r rv rm = vex_rrm op 0 0 r rv rm mempty

vex256_rrm :: Opcode -> Reg -> Reg -> RM -> Code
vex256_rrm op r rv rm = vex_rrm op 0 1 r rv rm mempty

vex256_rm :: Opcode -> Reg -> RM -> Code
vex256_rm op r rm = vex_rrm op 0 1 r NoReg rm mempty

vex256_mr :: Opcode -> RM -> Reg -> Code
vex256_mr op rm r = vex_rrm op 0 1 r NoReg rm mempty

vex256_rmi_slash :: Opcode -> Reg -> RM -> Word8 -> Code
vex256_rmi_slash op rv rm imval = vex_rrm op 0 1 (get_slash op) rv rm (b imval)

vex_rrm :: Opcode -> Word8 -> Word8 -> Reg -> Reg -> RM -> Code -> Code
vex_rrm op w l r rv rm imm =
    let
        m_mmmm = vexop_mmmmm op
        pp = vexop_pp op
        o = vexop_op op
        vx = vex r rv rm w m_mmmm l pp    --vex reg rm w m_mmmm l pp
    in
        vx <> b o <> modrm_sib_disp r rm <> imm

vex_misc :: Word8 -> Word8 -> Word8 -> Word8 -> Word8 -> Reg -> Reg -> RM -> Code -> Code
vex_misc w pp m_mmmm l op r rv rm imm =
    let
        vx = vex r rv rm w m_mmmm l pp    --vex reg rm w m_mmmm l pp
    in if r == NoReg && rm == NoRM then
        vx <> b op <> imm
    else
        vx <> b op <> modrm_sib_disp r rm <> imm

vexop_mmmmm :: Opcode -> Word8
vexop_mmmmm (I_66_0F38 _) = 2
vexop_mmmmm (I_66_0F _) = 1
vexop_mmmmm (I_66_0F_slash _ _) = 1
vexop_mmmmm (I_F3_0F _) = 1

vexop_pp :: Opcode -> Word8
vexop_pp (I_66_0F38 _) = 1
vexop_pp (I_66_0F _) = 1
vexop_pp (I_66_0F_slash _ _) = 1
vexop_pp (I_F3_0F _) = 2

vexop_op :: Opcode -> Word8
vexop_op (I_66_0F38 op) = op
vexop_op (I_66_0F op) = op
vexop_op (I_66_0F_slash op _) = op
vexop_op (I_F3_0F op) = op

get_slash :: Opcode -> Reg
get_slash (I_66_0F_slash _ r) = Slash r

------------------
evex256_rm :: Opcode -> Reg -> RM -> Code
evex256_rm (I_66_0F38 op) r rm =
    let
        vx = evex r rm 0 2 1 1
    in
        vx <> b op <> modrm_sib_disp r rm

------------------
get_r :: Reg -> Word8
get_r (Xmm reg) = reg .&. 7
get_r (Gpr reg) = reg .&. 7
get_r (Slash reg) = reg .&. 7

get_vvvv (Xmm reg) = 15 - (reg .&. 15)
get_vvvv NoReg = 15

get_ss :: Int -> Word8
get_ss 1 = 0
get_ss 2 = 1
get_ss 4 = 2
get_ss 8 = 3

get_index :: Reg -> Word8
get_index (Gpr 4) = error ("get_index: RSP cannot be used as index")
get_index (Gpr n) = n .&. 7
get_index NoReg = 4

get_base :: Reg -> Word8
get_base (Gpr n) = n .&. 7
get_base NoReg = 4

get_mod_and_disp_width_for_sib :: RM -> (Word8,Int)
get_mod_and_disp_width_for_sib (SibMem _ _ NoReg disp)
    | disp >= -0x80000000 && disp <= 0x7fffffff = (0,4)    -- mode 0 doesn't normally come with a disp, but in case b=5 it does
    | otherwise = error ("get_mod_for_disp: disp " ++ show disp ++ " is out of range")
get_mod_and_disp_width_for_sib (SibMem _ _ (Gpr b) disp)
    | b /= 5 && disp == 0 = (0,0)
    | disp >= -0x80 && disp <= 0x7f = (1,1)
    | disp >= -0x80000000 && disp <= 0x7fffffff = (2,4)
    | otherwise = error ("get_mod_for_disp: disp " ++ show disp ++ " is out of range")

modrm_sib_disp :: Reg -> RM -> Code
modrm_sib_disp reg (AbsMem addr) =
    let
        r = get_r reg
        mod = 0
        rm = 4
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
        base = 5
        index = 4
        ss = 0
        sib = (ss `shiftL` 6) .|. (index `shiftL` 3) .|. base
        disp = int_as_four_bytes addr
    in
        b modrm <> b sib <> disp

modrm_sib_disp reg (SibMem scale indexreg basereg displ) =
    let
        r = get_r reg
        (mod,width) = get_mod_and_disp_width_for_sib (SibMem scale indexreg basereg displ)
        rm = 4
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
        base = get_base basereg
        index = get_index indexreg
        ss = get_ss scale
        sib = (ss `shiftL` 6) .|. (index `shiftL` 3) .|. base
        disp = int_as_n_bytes width displ
    in
        b modrm <> b sib <> disp

{-
modrm_sib_disp reg (RegMem (Gpr 4) 0) =   -- RSP
    let
        r = get_r reg
        mod = 0
        rm = 4
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
        base = 4
        index = 4
        ss = 0
        sib = (ss `shiftL` 6) .|. (index `shiftL` 3) .|. base
    in
        b modrm <> b sib
-}
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
rex_r (Slash n) = 0
rex_r NoReg = 0

rex_x :: RM -> Word8
rex_x (R _) = 0
rex_x (AbsMem _) = 0
rex_x (RegMem (Gpr r) _) = 0
rex_x (SibMem _ (Gpr i) _ _)
    | i == 4 = error "rex_x: RSP being used as index"
    | otherwise = (i .&. 8) `shiftR` 3
rex_x (SibMem _ NoReg _ _) = 0
rex_x NoRM = 0

rex_b :: RM -> Word8
rex_b (R (Xmm n)) = (n .&. 8) `shiftR` 3
rex_b (R (Gpr n)) = (n .&. 8) `shiftR` 3
rex_b (AbsMem _) = 0
rex_b (RegMem (Gpr r) _)
    | r == 4 = error ("rex_b: detected RegMem RSP")
    | otherwise = (r .&. 8) `shiftR` 3
rex_b (SibMem _ _ (Gpr b) _) = (b .&. 8) `shiftR` 3
rex_b (SibMem _ _ NoReg _) = 0
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

vex :: Reg -> Reg -> RM -> Word8 -> Word8 -> Word8 -> Word8 -> Code
vex reg regv rm w m_mmmm l pp =
    let
        r = 1 - rex_r reg
        x = 1 - rex_x rm
        b' = 1 - rex_b rm
        vvvv = get_vvvv regv
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

evex :: Reg -> RM -> Word8 -> Word8 -> Word8 -> Word8 -> Code
evex reg rm w mm ll pp =
    let
        r = 1-rex_r reg
        x = 1-rex_x rm
        b' = 1-rex_b rm
        r' = 1
        vvvv = 15
        z = 0
        v' = 0
        aaa = 0
    in
        b 0x62 <>
            b ((r `shiftL` 7) .|. (x `shiftL` 6) .|. (b' `shiftL` 5) .|. (r' `shiftL` 4) .|. mm) <>
            b ((w `shiftL` 7) .|. (vvvv `shiftL` 3) .|. 4 .|. pp) <>
            b ((z `shiftL` 7) .|. (ll `shiftL` 5) .|. (v' `shiftL` 3) .|. aaa)

xmm_addr :: Reg -> Word8
xmm_addr (Xmm n) = n

int_as_n_bytes :: Int -> Int -> Code
int_as_n_bytes 0 0 = mempty
int_as_n_bytes 0 int = error ("int_as_n_bytes: " ++ show int ++ " left over")
int_as_n_bytes n int = b (fromIntegral (int .&. 0xff)) <> int_as_n_bytes (n-1) (int `shiftR` 8)

int_as_four_bytes :: Int -> Code
int_as_four_bytes int = int_as_n_bytes 4 int

