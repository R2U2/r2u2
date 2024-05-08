-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : divider_fsm.vhd
-- Author     : Thomas Reinbacher
-- Copyright  : 2012, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A unsigned integer divider, runs in NUM_OF_BITS clock cycles
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use work.cevLib_unsigned_pkg.all;
entity divider_fsm is
  
  generic (
    NUM_OF_BITS : integer); 
  port (
    clk       : in  std_logic;          -- clock
    reset_n   : in  std_logic;          -- active low reset
    run       : in  std_logic;          
    dividend  : in  std_logic_vector((NUM_OF_BITS - 1) downto 0);
    enable    : in  std_logic;
    divisor   : in  std_logic_vector((NUM_OF_BITS - 1) downto 0);
    quotient  : out std_logic_vector((NUM_OF_BITS - 1) downto 0);
    remainder : out std_logic_vector((NUM_OF_BITS - 1) downto 0);
    busy      : out std_logic;
    fin       : out std_logic); 

end divider_fsm;

architecture rtl of divider_fsm is
  type DIV_STATE is (ST_PRE,
                     ST_IDLE,
                     ST_FETCH_OPERANDS,
                     ST_DIVIDE);
  signal divider_state, divider_state_next : DIV_STATE;

  type registers_type is record
    dividend  : std_logic_vector((NUM_OF_BITS-1) downto 0);
    divisor   : std_logic_vector((NUM_OF_BITS-1) downto 0);
    quotient  : std_logic_vector((NUM_OF_BITS-1) downto 0);
    remainder : std_logic_vector((NUM_OF_BITS-1) downto 0);
    bitPos    : integer range 0 to NUM_OF_BITS+1;
    busy      : std_logic;
    fin       : std_logic;
  end record;
  signal s_reg, s_reg_next : registers_type;

  constant REG_DEFAULT : registers_type :=
    (divisor   => (others => '0'),
     dividend  => (others => '0'),
     quotient  => (others => '0'),
     remainder => (others => '0'),
     bitPos    => 0,
     busy      => '0',
     fin       => '0');

begin
  next_state : process (divider_state, run, enable, s_reg_next.bitPos)
  begin  -- process next_state
    divider_state_next <= divider_state;

    case divider_state is
      when ST_PRE =>
        if enable = '1' then
          divider_state_next <= ST_IDLE;
        end if;
        
      when ST_IDLE =>
        if run = '1' then
          divider_state_next <= ST_FETCH_OPERANDS;
        end if;

      when ST_FETCH_OPERANDS =>
        divider_state_next <= ST_DIVIDE;

      when ST_DIVIDE =>
        if s_reg_next.bitPos = 0 then
          divider_state_next <= ST_IDLE;
        end if;

      when others => null;
    end case;
  end process next_state;

  output : process (divider_state, s_reg, divisor, dividend)
  begin
    s_reg_next      <= s_reg;
    s_reg_next.fin  <= '0';

    case divider_state is
      when ST_PRE =>
        s_reg_next.busy <= '0';

      when ST_IDLE =>
        s_reg_next.busy <= '0';

      when ST_FETCH_OPERANDS =>
        s_reg_next.divisor  <= divisor;
        s_reg_next.dividend <= dividend;
        s_reg_next.bitPos   <= NUM_OF_BITS+1;
        s_reg_next.busy <= '1';
        
      when ST_DIVIDE =>
        s_reg_next.busy <= '1';

        if (s_reg.remainder >= s_reg.divisor) then
          s_reg_next.remainder <= shift_left((s_reg.remainder-s_reg.divisor), 1)(s_reg.remainder'high downto 1) & s_reg.dividend(s_reg.dividend'high);
          s_reg_next.quotient  <= s_reg.quotient(s_reg.quotient'high-1 downto 0) & '1';
        else
          s_reg_next.remainder <= s_reg.remainder(s_reg.remainder'high-1 downto 0) & s_reg.dividend(s_reg.dividend'high);
          s_reg_next.quotient  <= s_reg.quotient(s_reg.quotient'high-1 downto 0) & '0';
        end if;
        s_reg_next.bitPos   <= s_reg.bitPos - 1;
        s_reg_next.dividend <= shift_left(s_reg.dividend, 1);
        if(s_reg.bitPos = 1) then
          s_reg_next.fin <= '1';
        end if;

      when others => null;
    end case;
  end process output;

  sync : process (clk, reset_n)
  begin  -- process sync
    if reset_n = '0' then               -- asynchronous reset
      s_reg         <= REG_DEFAULT;
      divider_state <= ST_PRE;
    elsif clk'event and clk = '1' then  -- rising clock edge
      s_reg         <= s_reg_next;
      divider_state <= divider_state_next;
    end if;
  end process sync;

  quotient  <= s_reg.quotient;
  remainder <= s_reg.remainder;
  fin       <= s_reg.fin;
  busy      <= s_reg.busy;
end rtl;
