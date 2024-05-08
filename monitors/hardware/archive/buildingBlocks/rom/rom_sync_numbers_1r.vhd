----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  rom_synch_1r_beh                                               --
-- Project Name: DIDELU                                                         --
-- Description:  ROM - Architecture                                             --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.rom_pkg.all;

entity rom_sync_numbers_1r is
  generic
    (
      ADDR_WIDTH   : integer;
      DATA_WIDTH   : integer;
      INIT_PATTERN : rom_array_numbers
      );
  port
    (
      clk  : in  std_logic;
      addr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
      rd   : in  std_logic;
      data : out std_logic_vector(DATA_WIDTH - 1 downto 0)
      );
end entity rom_sync_numbers_1r;

----------------------------------------------------------------------------------
--                               ARCHITECTURE                                   --
----------------------------------------------------------------------------------

architecture beh of rom_sync_numbers_1r is
  constant rom : rom_array_numbers(0 to 2 ** ADDR_WIDTH - 1) := INIT_PATTERN;
begin

  --------------------------------------------------------------------
  --                    PROCESS : SYNC                              --
  --------------------------------------------------------------------
  
  sync : process(clk)
  begin
    if rising_edge(clk) then
      if rd = '1' then
        data <= rom(to_integer(unsigned(addr)));
      end if;
    end if;
  end process sync;
  
end architecture beh;

--- EOF  ---
