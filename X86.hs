module X86 where

import Data.Bits ((.&.),(.|.),shiftL,shiftR)

data Reg = Xmm Int | Gpr Int deriving Eq
data RM = R Reg | AbsMem Int | NoRM
data Opcode = I_66_0F Int | I_66_0F38 Int
data OpcodeO = Old_OI Int Int

------------------
movdqa_rm = I_66_0F 0x6f
mov_oi8 = Old_OI 1 0xb0 -- 0xb0 thru 0xb7
vpbroadcastb_rm = I_66_0F38 0x78
paddb_rm = I_66_0F 0xfc

------------------
sse_rm :: Opcode -> Reg -> RM -> [Int]
sse_rm (I_66_0F op) r rm = [0x66] ++ maybe_rex r rm 0 ++ [0x0f,op] ++ modrm_sib_disp r rm

old_oi :: OpcodeO -> Reg -> Int -> [Int]
old_oi (Old_OI imsize op) (Gpr reg) imval =
    let
        mrex = maybe_rex (Gpr reg) NoRM 0
        r = reg .&. 7
        op' = op + r
        imm = int_as_n_bytes imsize imval
    in
        mrex ++ [op'] ++ imm

vex128_rm :: Opcode -> Reg -> RM -> [Int]
vex128_rm (I_66_0F38 op) r rm =
    let
        vx = vex r rm 0 2 0 1    --vex reg rm w' m_mmmm l pp
    in
        vx ++ [op] ++ modrm_sib_disp r rm

------------------
get_r :: Reg -> Int
get_r (Xmm reg) = reg .&. 7
get_r (Gpr reg) = reg .&. 7

modrm_sib_disp :: Reg -> RM -> [Int]
modrm_sib_disp reg (AbsMem addr) =
    let
        r = get_r reg
        mod = 0
        rm = 4
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
        disp = int_as_four_bytes addr
    in
        [modrm] ++ disp
modrm_sib_disp reg (R reg') =
    let
        r = get_r reg
        rm = get_r reg'
        mod = 3
        modrm = (mod `shiftL` 6) .|. (r `shiftL` 3) .|. rm
    in
        [modrm]

rex_r :: Reg -> Int
rex_r (Xmm n) = (n .&. 8) `shiftR` 3
rex_r (Gpr n) = (n .&. 8) `shiftR` 3

rex_x (R _) = 0
rex_x (AbsMem _) = 0
rex_x NoRM = 0

rex_b (R (Xmm n)) = (n .&. 8) `shiftR` 3
rex_b (R (Gpr n)) = (n .&. 8) `shiftR` 3
rex_b (AbsMem _) = 0
rex_b NoRM = 0

maybe_rex :: Reg -> RM -> Int -> [Int]
maybe_rex reg rm w =
    let
        r = rex_r reg
        x = rex_x rm
        b = rex_b rm
        rex = 0x40 .|. (w `shiftL` 3) .|. (r `shiftL` 2) .|. (x `shiftL` 1) .|. b
    in
        if rex == 0x40 then
            []
        else
            [rex]

vex :: Reg -> RM -> Int -> Int -> Int -> Int -> [Int]
vex reg rm w' m_mmmm l pp =
    let
        r = 1 - rex_r reg
        w = 1 - w'
        x = 1 - rex_x rm
        b = 1 - rex_b rm
        vvvv = 15
    in
        if m_mmmm == 1 && w == 1 && x == 1 && b == 1 then
            -- two-byte vex
            [0xc5, (r `shiftL` 7) .|. (vvvv `shiftL` 3) .|. (l `shiftL` 2) .|. pp]
        else
            -- three-byte vex
            [0xc4,
                (r `shiftL` 7) .|. (x `shiftL` 6) .|. (b `shiftL` 5) .|. m_mmmm,
                (w `shiftL` 7) .|. (vvvv `shiftL` 3) .|. (l `shiftL` 2) .|. pp]

xmm_addr :: Reg -> Int
xmm_addr (Xmm n) = n

int_as_n_bytes :: Int -> Int -> [Int]
int_as_n_bytes 0 0 = []
int_as_n_bytes 0 int = error ("int_as_n_bytes: " ++ show int ++ " left over")
int_as_n_bytes n int = (int .&. 0xff) : int_as_n_bytes (n-1) (int `shiftR` 8)

int_as_four_bytes :: Int -> [Int]
int_as_four_bytes int = int_as_n_bytes 4 int

