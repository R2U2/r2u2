----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  rom_pkg                                                        --
-- Project Name: DIDELU                                                         --
-- Description:  ROM - Package                                                  --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

----------------------------------------------------------------------------------
--                                 PACKAGE                                      --
----------------------------------------------------------------------------------

package rom_pkg is
  -- bits are stored as a std_logic array
  type rom_array is array (natural range<>, natural range<>) of std_logic;
  type rom_array_char is array (natural range<>) of std_logic_vector(7 downto 0);
  type rom_array_numbers is array (natural range<>) of std_logic_vector((5*8)-1 downto 0);

  --------------------------------------------------------------------
  --                          COMPONENT                             --
  --------------------------------------------------------------------

  -- read only memory
  component rom_sync_1r is
    generic
      (
        -- address witdh
        ADDR_WIDTH   : integer;
        -- data width
        DATA_WIDTH   : integer;
        -- init data
        INIT_PATTERN : rom_array
        );
    port
      (
        clk : in std_logic;
        addr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rd   : in  std_logic;
        data : out std_logic_vector(DATA_WIDTH - 1 downto 0)
        );
  end component rom_sync_1r;
  
    -- read only memory
  component rom_sync_char_1r is
    generic
      (
        -- address witdh
        ADDR_WIDTH   : integer;
        -- data width
        DATA_WIDTH   : integer;
        -- init data
        INIT_PATTERN : rom_array_char
        );
    port
      (
        clk : in std_logic;
        addr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rd   : in  std_logic;
        data : out std_logic_vector(DATA_WIDTH - 1 downto 0)
        );
  end component rom_sync_char_1r;
  
      -- read only memory
  component rom_sync_numbers_1r is
    generic
      (
        -- address witdh
        ADDR_WIDTH   : integer;
        -- data width
        DATA_WIDTH   : integer;
        -- init data
        INIT_PATTERN : rom_array_numbers
        );
    port
      (
        clk : in std_logic;
        addr : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
        rd   : in  std_logic;
        data : out std_logic_vector(DATA_WIDTH - 1 downto 0)
        );
  end component rom_sync_numbers_1r;

  --------------------------------------------------------------------
  --                          FUNCTIONS                             --
  --------------------------------------------------------------------

  -- casts a rom array into a std_logic_vector
  function to_stdlogicvector (data : rom_array; item : integer) return std_logic_vector;
end package rom_pkg;

----------------------------------------------------------------------------------
--                            PACKAGE - BODY                                    --
----------------------------------------------------------------------------------

package body rom_pkg is

  --------------------------------------------------------------------
  --                          FUNCTIONS                             --
  --------------------------------------------------------------------

  -- casts a rom array into a std_logic_vector
  function to_stdlogicvector (data : rom_array; item : integer) return std_logic_vector is
    variable result : std_logic_vector(data'length(2) - 1 downto 0);
  begin
    for i in result'range loop
      result(i) := data(item, i);
    end loop;
    return result;
  end function to_stdlogicvector;
end package body rom_pkg;

--- EOF  ---
