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
--  RS232 transmit unit
--
--  Clean RTL. Only one clock.
--  Only 8N1 mode supported.
--
--  History
--  05.10.2004  Mihai Munteanu      First working version.
--  06.10.2004  Mihai Munteanu      Speed up. Resets cnt_3 with a load
--

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;



entity tx is
Port
(
  clk      : in std_logic;      -- main clock
  ck_en    : in std_logic;      -- clk enable. 3x faster than baud 
  reset    : in std_logic;                     -- main reset
  tx_out   : out std_logic;                    -- TX data
  d_in     : in std_logic_vector(7 downto 0);  -- byte tobe transmited
  load     : in std_logic;                     -- load signal for d_in 
  busy     : out std_logic                     -- '1' during transmission
);
end tx;

architecture RTL of tx is

signal data   : std_logic_vector(9 downto 0); -- includes stop and start bits

signal cnt_3  : std_logic_vector(1 downto 0); -- cnt divides by 3 ck_en freq
signal ck3_en       : std_logic;  -- clk enable 3x slower than ck_en

signal shift_en     : std_logic;   -- enables the shifting

signal byte_timer   : std_logic_vector(3 downto 0); -- counts the txmited bits

begin


    --
    -- Counter for dividing by 3 the ck_en. Generates ck3_en 
    --
    BIT_CNT_PROC: process(clk, reset)
    begin
        if (reset ='1') then
            cnt_3 <= "00";
        elsif(clk'event and clk = '1') then
            if(load = '1') then
                    cnt_3 <= "10";
            end if;
            if(ck_en ='1') then
                if (cnt_3 = "10") then
                    ck3_en <= '1';
                    cnt_3 <= "00";
                else
                    ck3_en <= '0';
                    cnt_3 <= cnt_3 + 1;
                end if;
            else
                ck3_en <= '0';
            end if;
        end if;
    end process;


    --
    --  Shift register
    --
    SHIFT_DATA: process (clk, reset, data)
    begin
        if (reset ='1') then
            data <= (OTHERS => '1');
        elsif clk'event and clk='1' then
            if (load='1' and shift_en = '0') then
                data <=  d_in & "01" ;   --"01" - idle tx folowed by start
            elsif(ck3_en = '1') then
                data <= '1' & data(9 downto 1);--'1' @ end for stp bit & idl tx
            end if;
        end if;
        tx_out <= data(0);
    end process;

    --
    --  Timer. Counts the number of bytes transmited
    --
    BYTE_TIME: process (clk, reset)
    begin
        if (reset ='1') then
            byte_timer <= (OTHERS => '0');
            shift_en <= '0';
        elsif clk'event and clk='1' then
            if (load='1') then
                byte_timer <=  (OTHERS => '0');
                shift_en <= '1';
            elsif( ck3_en = '1') then
                if (byte_timer = "1010") then
                    byte_timer <= "1010";
                    shift_en <= '0';
                else
                    byte_timer <= byte_timer + 1;
                    shift_en <= '1';
                end if;
            end if;
        end if;
    end process;

    busy <= shift_en;

end RTL;

