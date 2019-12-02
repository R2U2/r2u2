library ieee;
use ieee.std_logic_1164.all;

entity fsm_reference is
  generic (
    CLK_DIVISOR : integer);
  port (
    clk      : in  std_logic;
    reset_n  : in  std_logic;
    data     : out std_logic_vector(7 downto 0);
    data_new : out std_logic_vector(7 downto 0);
    rx       : in  std_logic);
end fsm_reference;

architecture rtl of fsm_reference is
  type STATE_TYPE is (STATE_IDLE,
                      STATE_WAIT_START_BIT,
                      STATE_GOTO_MIDDLE_OF_START_BIT,
                      STATE_MIDDLE_OF_START_BIT,
                      STATE_WAIT_DATA_BIT,
                      STATE_MIDDLE_OF_DATA_BIT,
                      STATE_WAIT_STOP_BIT,
                      STATE_MIDDLE_OF_STOP_BIT);    
  signal receiver_state, receiver_state_next : STATE_TYPE;

  -- declare state machine registers
  type registers_type is record
    data_int : std_logic_vector(7 downto 0);
    data_out : std_logic_vector(7 downto 0);
    clk_cnt  : integer range 0 to CLK_DIVISOR -1;
    bit_cnt  : integer range 0 to 8;
    data_new : std_logic;
  end record;
  signal s_reg, s_reg_next : registers_type;

  constant s_reg_default : registers_type :=
    (data_int => (others => '0'),
     data_out => (others => '0'),
     clk_cnt  => 0,
     bit_cnt  => 0,
     data_new => '0');

begin
  data <= s_reg.data_out;

-- Next State Logic, determines state transitions
  -- Do not set any output signals in this process, the only signal
  -- that is assigned a value here is the next_state variable!
  next_state : process(receiver_state, rx, s_reg.clk_cnt, s_reg.bit_cnt)
  begin
    -- default
    receiver_state_next <= receiver_state;

    case receiver_state is
      -- idle state - wait for start bit (0)
      when STATE_IDLE =>
        if rx = '1' then
          receiver_state_next <= STATE_WAIT_START_BIT;
        end if;
        -- if start bit is received 
      when STATE_WAIT_START_BIT =>
        if rx = '0' then
          receiver_state_next <= STATE_GOTO_MIDDLE_OF_START_BIT;
        end if;
        -- wait for a half of bit time
      when STATE_GOTO_MIDDLE_OF_START_BIT =>
        -- count to Clock Divisor/2 -2 - we don't count to -1 since the next state is a pre-state
        if s_reg.clk_cnt >= CLK_DIVISOR / 2 - 2 then
          receiver_state_next <= STATE_MIDDLE_OF_START_BIT;
        end if;
        -- pre state - receive middle of start bit (CLK_DIVISOR - 1)
      when STATE_MIDDLE_OF_START_BIT =>
        receiver_state_next <= STATE_WAIT_DATA_BIT;
        -- wait until middle of data bit
      when STATE_WAIT_DATA_BIT =>
        if s_reg.clk_cnt >= CLK_DIVISOR - 2 then
          receiver_state_next <= STATE_MIDDLE_OF_DATA_BIT;
        end if;
        -- pre state - receive middle of data bit
      when STATE_MIDDLE_OF_DATA_BIT =>
        -- if last bit has been received -> next bit will be stop bit
        if s_reg.bit_cnt = 7 then
          receiver_state_next <= STATE_WAIT_STOP_BIT;
          -- else receive next data bit
        else
          receiver_state_next <= STATE_WAIT_DATA_BIT;
        end if;
        -- wait until middle of stop bit
      when STATE_WAIT_STOP_BIT =>
        if s_reg.clk_cnt >= CLK_DIVISOR - 2 then
          receiver_state_next <= STATE_MIDDLE_OF_STOP_BIT;
        end if;
        -- receive middle of stop bit
      when STATE_MIDDLE_OF_STOP_BIT =>
        if rx = '1' then
          receiver_state_next <= STATE_WAIT_START_BIT;
        else
          receiver_state_next <= STATE_IDLE;
        end if;
    end case;
  end process next_state;

  -- output process
  -- Following the design principle of a Moore style Statemachine
  -- Each state has a dedicated output configuration. The output
  -- process is combinatorial and assigns the output values to the
  -- s_reg_next record. This is the only signal where we assign values
  -- in this process...
  output : process(receiver_state, s_reg, rx)
  begin
    -- assign the current output configuration to the configuration in
    -- the next state;
    s_reg_next          <= s_reg;
    s_reg_next.data_new <= '0';

    case receiver_state is
      -- IDLE - do nothing
      when STATE_IDLE =>
        null;
        -- reset all counters to 0
      when STATE_WAIT_START_BIT =>
        s_reg_next.bit_cnt <= 0;
        s_reg_next.clk_cnt <= 0;
        -- count until middle of bit time is reached
      when STATE_GOTO_MIDDLE_OF_START_BIT =>
        s_reg_next.clk_cnt <= s_reg.clk_cnt +1;
        -- reset clock counter
      when STATE_MIDDLE_OF_START_BIT =>
        s_reg_next.clk_cnt <= 0;
        -- count until middle of data bit time is reached
      when STATE_WAIT_DATA_BIT =>
        s_reg_next.clk_cnt <= s_reg.clk_cnt +1;
      when STATE_MIDDLE_OF_DATA_BIT =>
        s_reg_next.clk_cnt  <= 0;
        -- receive next bit
        s_reg_next.bit_cnt  <= s_reg.bit_cnt+1;
        -- buffer data 
        s_reg_next.data_int <= rx & s_reg.data_int(7 downto 1);
      when STATE_WAIT_STOP_BIT =>
        s_reg_next.clk_cnt <= s_reg.clk_cnt + 1;
        -- finished
      when STATE_MIDDLE_OF_STOP_BIT =>
        -- signalize new data
        s_reg_next.data_new <= '1';
        -- output new data
        s_reg_next.data_out <= s_reg.data_int;
    end case;
  end process output;

  -- sync process
  -- The sync process registers the ouput of the state machine
  sync : process (clk, reset_n)
  begin  -- process sync
    if reset_n = '0' then               -- asynchronous reset (active low)
      s_reg          <= s_reg_default;
      -- set the default state after a reset
      receiver_state <= STATE_IDLE;
    elsif clk'event and clk = '1' then  -- rising clock edge
      -- synchronize the output configuration of the output process to the
      -- present state registers.
      s_reg          <= s_reg_next;
      -- assign the next state to the present state variable
      receiver_state <= receiver_state_next;
    end if;
  end process sync;
end rtl;
