-------------------------------------------------------------------------------
-- Project    : R2U2 (Realizable Responsive Unobtrusive Unit)
-------------------------------------------------------------------------------
-- File       : R2U2_pkg.vhd
-------------------------------------------------------------------------------
-- Description:  Package for R2U2 constants and components.                    
------------------------------------------------------------------------------- 


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.std_logic_arith.all; 
use work.cevLib_unsigned_pkg.all;
use work.math_pkg.all;
use work.log_input_pkg.all;
use work.ft_monitor_pkg.all;
-- Uncomment the following library declaration if using
-- arithmetic functions with Signed or Unsigned values
--use IEEE.NUMERIC_STD.ALL;

-- Uncomment the following library declaration if instantiating
-- any Xilinx leaf cells in this code.
--library UNISIM;
--use UNISIM.VComponents.all;

package R2U2_pkg is

    type config_type is (idle, config_ac, config_fm_imem, config_fm_int, config_log_data);
    constant SETUP_DATA_WIDTH : integer := max(32, MEMBUS_DATA_WIDTH);--40
    constant SETUP_ADDR_WIDTH : integer := max(11, MEMBUS_ADDR_WIDTH);--11

    constant CONFIG_DATA_BYTE : integer := (SETUP_DATA_WIDTH-1) / 8 + 1;
    constant CONFIG_ADDR_BYTE : integer := (SETUP_ADDR_WIDTH-1) / 8 + 1;
    constant DATA_BYTE : integer := (LOG_DATA_WIDTH-1) / 8 + 1;
    constant TIMESTAMP_BYTE : integer := (TIMESTAMP_WIDTH-1)/8 + 1;

    constant SETUP_DATA_WIDTH_extend : integer := CONFIG_DATA_BYTE*8;
    constant SETUP_ADDR_WIDTH_extend : integer := CONFIG_ADDR_BYTE*8;
    constant DATA_BYTE_WIDTH_extend : integer := DATA_BYTE*8;
    constant TIMESTAMP_WIDTH_extend : integer := TIMESTAMP_BYTE*8;

    component R2U2 is
            port ( 
                clk : in std_logic;
                rst : in std_logic;
                ConfigSTATE : in config_type;
                input_rdy : in std_logic;
                setup_addr : in std_logic_vector(SETUP_ADDR_WIDTH-1 downto 0);
                setup_data : in std_logic_vector(SETUP_DATA_WIDTH-1 downto 0);
                data : in std_logic_vector(LOG_DATA_WIDTH-1 downto 0);
                debug : out debug_t;
                res_verdict: out std_logic;
                res_timestamp : out std_logic_vector(TIMESTAMP_WIDTH-1 downto 0);
                res_rdy : out std_logic;
                res_exist : out std_logic
                );
    end component;

end package;

package body R2U2_pkg is

end R2U2_pkg;