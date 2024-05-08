----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  serial_port_receiver_beh                                       --
-- Project Name: DIDELU                                                         --
-- Description:  Serial Receiver - Architecture                                 --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

----------------------------------------------------------------------------------
--                               ARCHITECTURE                                   --
----------------------------------------------------------------------------------

architecture beh of serial_port_receiver is
  type RECEIVER_STATE_TYPE is (RECEIVER_STATE_IDLE, 
                               RECEIVER_STATE_WAIT_START_BIT,
                               RECEIVER_STATE_GOTO_MIDDLE_OF_START_BIT,
                               RECEIVER_STATE_MIDDLE_OF_START_BIT,
                               RECEIVER_STATE_WAIT_DATA_BIT,
                               RECEIVER_STATE_MIDDLE_OF_DATA_BIT,
                               RECEIVER_STATE_WAIT_STOP_BIT,
                               RECEIVER_STATE_MIDDLE_OF_STOP_BIT);
  signal receiver_state, receiver_state_next : RECEIVER_STATE_TYPE;
  signal data_int, data_int_next, data_out_int, data_out_next : std_logic_vector(7 downto 0);
  signal data_new_next : std_logic;
  signal clk_cnt, clk_cnt_next : integer range 0 to CLK_DIVISOR - 1;
  signal bit_cnt : integer range 0 to 8;
  signal bit_cnt_next : integer range 0 to 8;
begin
  data <= data_out_int;

  --------------------------------------------------------------------
  --                    PROCESS : NEXT_STATE                        --
  --------------------------------------------------------------------
  
  receiver_next_state : process(receiver_state, rx, clk_cnt, bit_cnt)
  begin
    -- default
    receiver_state_next <= receiver_state;

    case receiver_state is
      -- idle state - wait for start bit (0)
      when RECEIVER_STATE_IDLE =>
        if rx = '1' then
          receiver_state_next <= RECEIVER_STATE_WAIT_START_BIT;
        end if;
      -- if start bit is received 
      when RECEIVER_STATE_WAIT_START_BIT =>
        if rx = '0' then
          receiver_state_next <= RECEIVER_STATE_GOTO_MIDDLE_OF_START_BIT;
        end if;
      -- wait for a half of bit time
      when RECEIVER_STATE_GOTO_MIDDLE_OF_START_BIT =>
        -- count to Clock Divisor/2 -2 - we don't count to -1 since the next state is a pre-state
        if clk_cnt >= CLK_DIVISOR / 2 - 2 then
          receiver_state_next <= RECEIVER_STATE_MIDDLE_OF_START_BIT;
        end if;
      -- pre state - receive middle of start bit (CLK_DIVISOR - 1)
      when RECEIVER_STATE_MIDDLE_OF_START_BIT =>
        receiver_state_next <= RECEIVER_STATE_WAIT_DATA_BIT;
      -- wait until middle of data bit
      when RECEIVER_STATE_WAIT_DATA_BIT =>
        if clk_cnt >= CLK_DIVISOR - 2 then
          receiver_state_next <= RECEIVER_STATE_MIDDLE_OF_DATA_BIT;
        end if;
      -- pre state - receive middle of data bit
      when RECEIVER_STATE_MIDDLE_OF_DATA_BIT =>
        -- if last bit has been received -> next bit will be stop bit
        if bit_cnt = 7 then
          receiver_state_next <= RECEIVER_STATE_WAIT_STOP_BIT;
        -- else receive next data bit
        else
          receiver_state_next <= RECEIVER_STATE_WAIT_DATA_BIT;
        end if;
      -- wait until middle of stop bit
      when RECEIVER_STATE_WAIT_STOP_BIT =>
        if clk_cnt >= CLK_DIVISOR - 2 then
          receiver_state_next <= RECEIVER_STATE_MIDDLE_OF_STOP_BIT;
        end if;
      -- receive middle of stop bit
      when RECEIVER_STATE_MIDDLE_OF_STOP_BIT =>
		  if rx = '1' then
          receiver_state_next <= RECEIVER_STATE_WAIT_START_BIT;
		  else
		    receiver_state_next <= RECEIVER_STATE_IDLE;
		  end if;
    end case;
  end process receiver_next_state;
  
  --------------------------------------------------------------------
  --                    PROCESS : OUTPUT                            --
  --------------------------------------------------------------------  
  
  receiver_output : process(receiver_state, clk_cnt, bit_cnt, data_int, data_out_int, rx)
  begin
    clk_cnt_next <= clk_cnt;
    bit_cnt_next <= bit_cnt;
    data_int_next <= data_int;
    data_new_next <= '0';
    data_out_next <= data_out_int;
    
    case receiver_state is
      -- IDLE - do nothing
      when RECEIVER_STATE_IDLE =>
        null;
      -- reset all counters to 0
      when RECEIVER_STATE_WAIT_START_BIT =>
        bit_cnt_next <= 0;
        clk_cnt_next <= 0;
      -- count until middle of bit time is reached
      when RECEIVER_STATE_GOTO_MIDDLE_OF_START_BIT =>
        clk_cnt_next <= clk_cnt + 1;
      -- reset clock counter
      when RECEIVER_STATE_MIDDLE_OF_START_BIT =>
        clk_cnt_next <= 0;
      -- count until middle of data bit time is reached
      when RECEIVER_STATE_WAIT_DATA_BIT =>
        clk_cnt_next <= clk_cnt + 1;
      when RECEIVER_STATE_MIDDLE_OF_DATA_BIT =>
        clk_cnt_next <= 0;
        -- receive next bit
        bit_cnt_next <= bit_cnt + 1;
        -- buffer data 
        data_int_next <= rx & data_int(7 downto 1);
      when RECEIVER_STATE_WAIT_STOP_BIT =>
        clk_cnt_next <= clk_cnt + 1;
      -- finished
      when RECEIVER_STATE_MIDDLE_OF_STOP_BIT =>
        -- signalize new data
        data_new_next <= '1';
        -- output new data
        data_out_next <= data_int;
    end case;
  end process receiver_output;
  
  --------------------------------------------------------------------
  --                    PROCESS : SYNC                              --
  --------------------------------------------------------------------
  
  sync : process(clk, res_n)
  begin
    if res_n = '0' then
      clk_cnt <= 0;
      bit_cnt <= 0;
      data_int <= (others => '0');
      receiver_state <= RECEIVER_STATE_IDLE;
      data_new <= '0';
      data_out_int <= (others => '0');
    elsif rising_edge(clk) then
      clk_cnt <= clk_cnt_next;
      bit_cnt <= bit_cnt_next;
      data_int <= data_int_next;
      receiver_state <= receiver_state_next;
      data_new <= data_new_next;
      data_out_int <= data_out_next;
    end if;
  end process sync;
end architecture beh;

--- EOF ---
