----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  serial_port_transmitter_beh                                    --
-- Project Name: DIDELU                                                         --
-- Description:  Serial Transmitter - Architecture                              --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

----------------------------------------------------------------------------------
--                               ARCHITECTURE                                   --
----------------------------------------------------------------------------------

architecture beh of serial_port_transmitter is
  type TRANSMITTER_STATE_TYPE is (TRANSMITTER_STATE_IDLE,
                                  TRANSMITTER_STATE_NEW_DATA,
                                  TRANSMITTER_STATE_SEND_START_BIT,
                                  TRANSMITTER_STATE_TRANSMIT_FIRST,
                                  TRANSMITTER_STATE_TRANSMIT_NEXT,
                                  TRANSMITTER_STATE_TRANSMIT,
                                  TRANSMITTER_STATE_TRANSMIT_STOP_NEXT,
                                  TRANSMITTER_STATE_TRANSMIT_STOP);
  signal transmitter_state, transmitter_state_next : TRANSMITTER_STATE_TYPE;
  signal bit_cnt, bit_cnt_next : integer range 0 to 8;
  signal clk_cnt, clk_cnt_next : integer range 0 to CLK_DIVISOR - 1;
  signal rd_next, tx_next : std_logic;
  signal transmit_data, transmit_data_next : std_logic_vector(7 downto 0);
begin

  --------------------------------------------------------------------
  --                    PROCESS : NEXT_STATE                        --
  --------------------------------------------------------------------

  transmitter_next_state : process(transmitter_state, clk_cnt, bit_cnt, empty)
  begin
    transmitter_state_next <= transmitter_state;

    case transmitter_state is
      when TRANSMITTER_STATE_IDLE =>
        -- if there is data in the transmit buffer
        if empty = '0' then
          transmitter_state_next <= TRANSMITTER_STATE_NEW_DATA;
        end if;
      -- pre state before starting to send
      when TRANSMITTER_STATE_NEW_DATA =>
        transmitter_state_next <= TRANSMITTER_STATE_SEND_START_BIT;
      -- send start bit
      when TRANSMITTER_STATE_SEND_START_BIT =>
        -- count to Clock Divisor -2 -> we don't count to -1 since the next state is a pre-state
        -- which still will output the start bit
        if clk_cnt = CLK_DIVISOR - 2 then
          transmitter_state_next <= TRANSMITTER_STATE_TRANSMIT_FIRST;
        end if;
      -- pre state
      when TRANSMITTER_STATE_TRANSMIT_FIRST =>
        transmitter_state_next <= TRANSMITTER_STATE_TRANSMIT;
      -- pre state - next state will transmit next data bit  
      when TRANSMITTER_STATE_TRANSMIT_NEXT =>
        transmitter_state_next <= TRANSMITTER_STATE_TRANSMIT;
      -- send data bit for specified time
      when TRANSMITTER_STATE_TRANSMIT =>
        if clk_cnt = CLK_DIVISOR - 2 then
          -- if last bit is reached
          if bit_cnt = 7 then
            transmitter_state_next <= TRANSMITTER_STATE_TRANSMIT_STOP_NEXT;
          -- if last bit is not reached
          else
            transmitter_state_next <= TRANSMITTER_STATE_TRANSMIT_NEXT;
          end if;
        end if;
      -- pre state - next state will send stop bit
      when TRANSMITTER_STATE_TRANSMIT_STOP_NEXT =>
        transmitter_state_next <= TRANSMITTER_STATE_TRANSMIT_STOP;
      -- send stop bit
      when TRANSMITTER_STATE_TRANSMIT_STOP =>
        if clk_cnt = CLK_DIVISOR - 2 then
          -- if the buffer is not empty - new data has to be transmitted
          if empty = '0' then
            transmitter_state_next <= TRANSMITTER_STATE_NEW_DATA;    
          -- else nothing to do -> go IDLE
          else          
            transmitter_state_next <= TRANSMITTER_STATE_IDLE;
          end if;
        end if;
    end case;
  end process transmitter_next_state;
  
  --------------------------------------------------------------------
  --                    PROCESS : OUTPUT                            --
  --------------------------------------------------------------------  
  
  transmitter_output : process(transmitter_state, clk_cnt, bit_cnt, data, transmit_data)
  begin
    clk_cnt_next <= clk_cnt;
    bit_cnt_next <= bit_cnt;
    tx_next <= '1';
    rd_next <= '0';
    transmit_data_next <= transmit_data;

    case transmitter_state is
      -- last transmission has been finished and transmitter is idle and ready to send new data
      when TRANSMITTER_STATE_IDLE =>
        null;
      when TRANSMITTER_STATE_NEW_DATA =>
        -- get the next data byte from the FIFO buffer
        rd_next <= '1';
        -- clock counter is resetted to 0
        clk_cnt_next <= 0;
      when TRANSMITTER_STATE_SEND_START_BIT =>
        -- transmit start bit
        clk_cnt_next <= clk_cnt + 1;
        tx_next <= '0';
      when TRANSMITTER_STATE_TRANSMIT_FIRST =>
        clk_cnt_next <= 0;
        -- set bit count to 0
        bit_cnt_next <= 0;
        -- still transmit start bit
        tx_next <= '0';
        transmit_data_next <= data;
      when TRANSMITTER_STATE_TRANSMIT_NEXT =>
        clk_cnt_next <= 0;
        bit_cnt_next <= bit_cnt + 1;
        -- send data bit
        tx_next <= transmit_data(0);
        -- prepare new data bit
        transmit_data_next(6 downto 0) <= transmit_data(7 downto 1);
      when TRANSMITTER_STATE_TRANSMIT =>
        clk_cnt_next <= clk_cnt + 1;
        -- send data bit
        tx_next <= transmit_data(0);
      -- send last bit
      when TRANSMITTER_STATE_TRANSMIT_STOP_NEXT =>
        clk_cnt_next <= 0;
        tx_next <= transmit_data(0);
      -- send stop bit (1)
      when TRANSMITTER_STATE_TRANSMIT_STOP =>
        clk_cnt_next <= clk_cnt + 1;
    end case;
  end process transmitter_output;
    
  --------------------------------------------------------------------
  --                    PROCESS : SYNC                              --
  --------------------------------------------------------------------
  
  sync : process(clk, res_n)
  begin
    if res_n = '0' then
      transmitter_state <= TRANSMITTER_STATE_IDLE;
      clk_cnt <= 0;
      transmit_data <= (others => '0');
      bit_cnt <= 0;
      tx <= '1';
      rd <= '0';
    elsif rising_edge(clk) then
      transmitter_state <= transmitter_state_next;
      clk_cnt <= clk_cnt_next;
      transmit_data <= transmit_data_next;
      tx <= tx_next;
      bit_cnt <= bit_cnt_next;
      rd <= rd_next;
    end if;
  end process sync;
end architecture beh;

--- EOF ---