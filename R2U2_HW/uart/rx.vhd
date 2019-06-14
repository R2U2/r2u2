--
-- Copyright (C) 2004  Mihai Munteanu
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
-- 
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program; if not, write to the Free Software
-- Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
--
-- You can contact me at:
-- http://www.hp-h.com/p/munte
--

--
--  RS232 receive unit
--
--  Clean RTL. Only one clock.
--  Only 8N1 mode supported. Uses a big state machine - Easy to extend
--
--  History
--  03.11.2004  Mihai Munteanu      First working version.
--  05.11.2004  Mihai Munteanu      Correcter full flag behaviour
--

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;


entity RX is
Port
(
  rx_in   : in std_logic;       -- Serial data in 
  clk     : in std_logic;       -- Main clock. Rising edge 
  ck_en   : in std_logic;       -- Clock enable. Must be 3x faster than baud
  reset   : in std_logic;       -- Main Reset
  d_out   : out std_logic_vector(7 downto 0);     -- Received byte
  full    : out std_logic;      -- Flag indicating that a byte was received
  full_clr: in  std_logic       -- Clears the full flag
    );
end RX;

architecture RTL of RX is

    type STATE_TYPE is (IDLE,
                        START_START,    START_END,
                        B0_START,       B0_SAMPLE,      B0_END,
                        B1_START,       B1_SAMPLE,      B1_END,
                        B2_START,       B2_SAMPLE,      B2_END,
                        B3_START,       B3_SAMPLE,      B3_END,
                        B4_START,       B4_SAMPLE,      B4_END,
                        B5_START,       B5_SAMPLE,      B5_END,
                        B6_START,       B6_SAMPLE,      B6_END,
                        B7_START,       B7_SAMPLE,      B7_END,
                        STOP
                        );

signal CS, NS: STATE_TYPE;    -- current andnext state

signal rx_shift_reg : std_logic_vector(7 downto 0); -- data reg.RX shifted here
signal rx_shift_en          : std_logic;  -- enables the rx shift

signal d_out_valid          : std_logic;  -- active in stop and idle mode
signal d_out_valid_delayed  : std_logic;
signal d_out_valid_r_edge   : std_logic; -- indicates rising edge

begin

    --
    -- Rising edge detection
    --
    D_OUT_VALID_REDG: process (clk, reset)
    begin
        if (reset ='1') then
            d_out_valid_delayed <= '1';
        elsif (clk'event and clk = '1') then
            d_out_valid_delayed <= d_out_valid;
        end if;
    end process;

    d_out_valid_r_edge <= d_out_valid and (not d_out_valid_delayed);


    --
    -- full flag handling
    --
    FULL_FLAG : process (clk, reset)
    begin
        if (reset ='1') then
            full <= '0';
        elsif (clk'event and clk = '1') then
            if( full_clr = '1' or rx_shift_en= '1' ) then
                full <= '0';
            elsif (d_out_valid_r_edge = '1') then
                full <= '1';
            end if;
        end if;
    end process;


    --
    -- Serial to parallel shift register
    --
    RX_SHIFT: process (clk, reset)
    begin
        if (reset ='1') then
            rx_shift_reg <= (OTHERS => '0');
        elsif (clk'event and clk = '1') then
            if(rx_shift_en='1' and ck_en='1') THEN
                rx_shift_reg <= rx_in & rx_shift_reg(7 downto 1);
            end if;
        end if;
    end process;
    d_out <= rx_shift_reg;


    --
    -- Synchronous part of the receive state machine 
    --
    SYNC_PROC: process (clk, reset)
    begin
        if (reset ='1') then
            CS <= IDLE;
        elsif (clk'event and clk = '1') then
            if(ck_en ='1') THEN
                CS <= NS;
            end if;
        end if;
    end process;


    --
    -- Receive state machine
    --
    COMB_PROC: process (CS, rx_in)
    begin
       case CS is
            when IDLE =>

                rx_shift_en <= '0';
                d_out_valid <= '1';

                if ( rx_in = '0' ) then
                    NS <= START_START;
                else
                    NS <= IDLE;
                end if;
            --------------------------
            when START_START =>
                rx_shift_en <= '0';
                d_out_valid <= '1';
                NS <= START_END;
            when START_END =>
                d_out_valid <= '0';
                rx_shift_en <= '0';
                NS <= B0_START;
            --------------------------
            when B0_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B0_SAMPLE;
            when B0_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B0_END;
            when B0_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B1_START;
            --------------------------
            when B1_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B1_SAMPLE;
            when B1_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B1_END;
            when B1_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B2_START;
            --------------------------
            when B2_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B2_SAMPLE;
            when B2_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B2_END;
            when B2_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B3_START;
            --------------------------
            when B3_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B3_SAMPLE;
            when B3_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B3_END;
            when B3_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B4_START;
            --------------------------
            when B4_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B4_SAMPLE;
            when B4_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B4_END;
            when B4_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B5_START;
            --------------------------
            when B5_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B5_SAMPLE;
            when B5_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B5_END;
            when B5_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B6_START;
            --------------------------
            when B6_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B6_SAMPLE;
            when B6_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B6_END;
            when B6_END =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B7_START;
            --------------------------
            when B7_START =>
                rx_shift_en <= '0';
                d_out_valid <= '0';
                NS <= B7_SAMPLE;
            when B7_SAMPLE =>
                rx_shift_en <= '1';
                d_out_valid <= '0';
                NS <= B7_END;
            when B7_END =>
                rx_shift_en <= '0';
                d_out_valid <= '1';
                NS <= STOP;
            --------------------------
            when STOP =>
                rx_shift_en <= '0';
                d_out_valid <= '1';
                NS  <= IDLE;
       end case;
    end process;

end RTL;
