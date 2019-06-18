library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package log_input_pkg is
    constant ATOMICS_WIDTH : integer := 2;
    constant ATC_ADDR_WIDTH : integer := 11;
    constant ATC_DATA_WIDTH : integer := 32;
    constant LOG_DATA_WIDTH : integer := 38;

    component at_checkers is
        port(
            clk          : in std_logic;
            rst_n        : in std_logic;
            config_addr  : in std_logic_vector(11-1 downto 0);
            config_data  : in std_logic_vector(32-1 downto 0);
            config_write : in std_logic;
            sample_clk   : in std_logic;
            data         : in std_logic_vector(LOG_DATA_WIDTH-1 downto 0);
            atomics      : out std_logic_vector(ATOMICS_WIDTH-1 downto 0)
        );
    end component;

    -- APS1 radius
    constant APS1_WIDTH : integer := 19;
    function get_APS1 (input : std_logic_vector(38-1 downto 0)) return std_logic_vector;

    -- APS2 radius
    constant APS2_WIDTH : integer := 19;
    function get_APS2 (input : std_logic_vector(38-1 downto 0)) return std_logic_vector;

end log_input_pkg;

package body log_input_pkg is
    -- APS1 radius
    function get_APS1 (input : std_logic_vector(38-1 downto 0)) return std_logic_vector is
    begin
        return input(38-1 downto 19);
    end function;

    -- APS2 radius
    function get_APS2 (input : std_logic_vector(38-1 downto 0)) return std_logic_vector is
    begin
        return input(19-1 downto 0);
    end function;

end package body;
