-------------------------------------------------------------------------------
-- Project    : CevTes RVU (Runtime Verification Unit)
-------------------------------------------------------------------------------
-- File       : timer_fsm.vhd
-- Author     : Thomas Reinbacher
--              Johannes Geist           johannes.geist@technikum-wien.at
-- Copyright  : 2011, Thomas Reinbacher (treinbacher@ecs.tuwien.ac.at)
--              Vienna University of Technology, ECS Group
-------------------------------------------------------------------------------
-- Description: A generic Timer with different wait times during runtime,
--              specified with the period signal. The time base can be
--              specified with the TICK generic. for further info see the table.              
--                   for    128MHz |  160MHz
--                 -------------------------
--                 100ns |     n/a  |       16
--                   1µs |      128 |      160
--                  10µs |     1280 |     1600
--                 100µs |    12800 |    16000
--                   1ms |   128000 |   160000
--                  10ms |  1280000 |  1600000
--                 100ms | 12800000 | 16000000
--                   1s  |128000000 |160000000
--              The time measured is taken between go signal and expired signal.
-------------------------------------------------------------------------------
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity timer_fsm is
  
  generic (
    TIMER_WIDTH : integer;
    TICK        : integer);             -- Clock cycle ticks for one period

  port (
    clk       : in  std_logic;          -- clock
    reset_n   : in  std_logic;          -- active low reset
    go        : in  std_logic;          -- timer go signal
    stop      : in  std_logic;          -- timer stop signal
    expired   : out std_logic;          -- timer expired signal
    period    : in  std_logic_vector((TIMER_WIDTH - 1) downto 0);  -- the time which should be
                                                                   -- waited
    remaining : out std_logic_vector((TIMER_WIDTH - 1) downto 0));  -- if the timer is stopped
                                        -- the left timeunits
   

end timer_fsm;

architecture rtl of timer_fsm is

  component clk_div
    generic (
      PRESCALER_WIDTH : integer);
    port (
      clk       : in  std_logic;
      reset_n   : in  std_logic;
      en        : in  std_logic;
      clk_div   : out std_logic;
      prescaler : in  std_logic_vector(PRESCALER_WIDTH downto 0));
  end component;

  type TMR_STATE is(STATE_IDLE,
                    STATE_RUN_EN,
                    STATE_WAIT_FOR_TICK,
                    STATE_COUNT,
                    STATE_EXPIRED,
                    STATE_STOPPED);
  signal timer_state, timer_state_next : TMR_STATE;

  constant PRESCALER_WIDTH : integer := 27;

  type registers_type is record
    expired     : std_logic;
    remaining   : std_logic_vector((TIMER_WIDTH - 1) downto 0);
    timer_ctr   : std_logic_vector((TIMER_WIDTH - 1) downto 0);
    timebase_en : std_logic;
    compensate  : std_logic;
    prescaler   : std_logic_vector((PRESCALER_WIDTH) downto 0);
  end record;
  signal s_reg, s_reg_next : registers_type;

  signal s_tick_en : std_logic;

  constant s_reg_default : registers_type :=
    (expired     => '0',
     remaining   => (others => '0'),
     timer_ctr   => (others => '0'),
     timebase_en => '0',
     compensate  => '0',
     prescaler   => (others => '0'));

begin

  expired   <= s_reg.expired;
  remaining <= s_reg.remaining;

  i_clk_div : clk_div
    generic map (
      PRESCALER_WIDTH => PRESCALER_WIDTH)
    port map (
      clk       => clk,
      reset_n   => reset_n,
      en        => s_reg.timebase_en,
      clk_div   => s_tick_en,
      prescaler => s_reg.prescaler);

  next_state : process (timer_state, go, stop, s_reg, s_tick_en)
  begin  -- process next_state
    timer_state_next <= timer_state;
    case timer_state is
      when STATE_IDLE =>
        if go = '1' and stop = '0' and TICK > 5 then
          timer_state_next <= STATE_RUN_EN;
        elsif stop = '1' then
          timer_state_next <= STATE_STOPPED;
        end if;
      when STATE_RUN_EN =>
        if stop = '1' then
          timer_state_next <= STATE_STOPPED;
        else
          timer_state_next <= STATE_WAIT_FOR_TICK;
        end if;
      when STATE_WAIT_FOR_TICK =>
        if stop = '1' then
          timer_state_next <= STATE_STOPPED;
        elsif s_tick_en = '1'then
          timer_state_next <= STATE_COUNT;
        end if;
      when STATE_COUNT =>
        if stop = '1' then
          timer_state_next <= STATE_STOPPED;
        elsif s_reg.timer_ctr = 1 then
          timer_state_next <= STATE_EXPIRED;
        else
          timer_state_next <= STATE_WAIT_FOR_TICK;
        end if;
      when STATE_EXPIRED | STATE_STOPPED =>
        if stop = '1' then
          timer_state_next <= STATE_STOPPED;
        else
          timer_state_next <= STATE_IDLE;
        end if;
      when others => null;
    end case;
  end process next_state;

  output : process (timer_state, s_reg, period)
  begin  -- process output
    s_reg_next         <= s_reg;
    s_reg_next.expired <= '0';
    case timer_state is
      when STATE_IDLE =>
        s_reg_next.timer_ctr <= period;
        -- we need to adapt the period here to compensate state changes from COUNT to EXPIRED / STOPPED
        s_reg_next.prescaler <= conv_std_logic_vector((TICK - 6), (PRESCALER_WIDTH + 1));
      when STATE_RUN_EN =>
        s_reg_next.timebase_en <= '1';
      when STATE_WAIT_FOR_TICK =>
        if s_reg.compensate = '1' then
          s_reg_next.prescaler <= conv_std_logic_vector((TICK - 1), (PRESCALER_WIDTH + 1));
        end if;
      when STATE_COUNT =>
        s_reg_next.timer_ctr  <= s_reg.timer_ctr - '1';
        s_reg_next.compensate <= '1';
      when STATE_EXPIRED =>
        s_reg_next.expired     <= '1';
        s_reg_next.timer_ctr   <= (others => '0');
        s_reg_next.timebase_en <= '0';
        s_reg_next.compensate  <= '0';
      when STATE_STOPPED =>
        s_reg_next.remaining   <= s_reg.timer_ctr;
        s_reg_next.timer_ctr   <= (others => '0');
        s_reg_next.timebase_en <= '0';
        s_reg_next.compensate  <= '0';
      when others => null;
    end case;
  end process output;

  sync : process (clk, reset_n)
  begin  -- process sync
    if reset_n = '0' then               -- asynchronous reset
      s_reg       <= s_reg_default;
      timer_state <= STATE_IDLE;
    elsif clk'event and clk = '1' then  -- rising clock edge
      s_reg       <= s_reg_next;
      timer_state <= timer_state_next;
    end if;
  end process sync;

end rtl;
