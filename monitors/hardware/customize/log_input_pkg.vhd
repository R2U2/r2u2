library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package log_input_pkg is
    constant ATOMICS_WIDTH : integer := 2;
    constant ATC_ADDR_WIDTH : integer := 11;
    constant ATC_DATA_WIDTH : integer := 32;
    constant LOG_DATA_WIDTH : integer := 38;

    -- APS1 radius
    constant APS1_WIDTH : integer := 19;
    function get_APS1 (input : std_logic_vector(38-1 downto 0)) return std_logic_vector;

    -- APS2 radius
    constant APS2_WIDTH : integer := 19;
    function get_APS2 (input : std_logic_vector(38-1 downto 0)) return std_logic_vector;

    component sensor_log is
    port ( 
        clk       : in  STD_LOGIC;
        reset     : in STD_LOGIC;
        pRBUS_DATA : in std_logic_vector(15 downto 0);
        pRBUS_ADDR : in std_logic_vector(7 downto 0);
        pRBUS_EN : in std_logic;
        data_update : out std_logic;
        test_data : out std_logic_vector(31 downto 0);
        log_data : out std_logic_vector(LOG_DATA_WIDTH-1 downto 0)
            );
end component;

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
