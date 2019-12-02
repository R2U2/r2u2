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
--  Counter for generating a clock enable signal
--
--  History
--  03.10.2004  Mihai Munteanu      First version.
--  07.10.2004  Mihai Munteanu      Added reste value for ck_en
--

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;


entity baud_cnt is
Port
(
  clk       : in std_logic;            -- Main clock. Rising edge 
  reset     : in std_logic;                     -- Main Reset
  cnt_limit : in std_logic_vector(15 downto 0); -- Cntr limit=freq div factor 
  ck_en     : out std_logic -- Clock enable. Must be 3x faster than baud rate
);
end baud_cnt;

architecture RTL of baud_cnt is

    signal counter :  std_logic_vector(15 downto 0);

begin

    --
    -- Counter for generating ck_en 
    --
    BAUD_CNT: process(clk, reset)
    begin
        if (reset ='1') then
            counter <= "0000000000000001";
            ck_en <= '0';
        elsif(clk'event and clk = '1') then
            if (counter = "0000000000000001") then
                ck_en <= '1';
                counter <= cnt_limit;
            else
                ck_en <= '0';
                counter <= counter - 1;
            end if;
        end if;
    end process;


end RTL;
