library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.at_checker_pkg.all;
use work.log_input_pkg.all;
--use work.filter_pkg.all;

entity at_checkers is
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
end entity;

architecture arch of at_checkers is
    signal APS1                 : std_logic_vector(19-1 downto 0);
    signal APS2                 : std_logic_vector(19-1 downto 0);

    signal write0 : std_logic;
    signal write1 : std_logic;


begin
    APS1                 <= get_APS1(data);
    APS2                 <= get_APS2(data);

    process(config_write, config_addr) is
    begin
        write0 <= '0';
        write1 <= '0';

        case config_addr(11-1 downto 3) is
            when "00000000" =>
                write0 <= config_write;
            when "00000001" =>
                write1 <= config_write;
            when others =>
                null;
        end case;

    end process;

    atc_0 : at_checker
    generic map (
        IN_1_WIDTH => APS1_WIDTH,
        IN_2_WIDTH => APS2_WIDTH,
        ADDR       => 0
    )
    port map(
        clk   => clk,
        rst_n => rst_n,
        config_addr  => config_addr(3-1 downto 0),
        config_data  => config_data,
        config_write => write0,
        in1   => APS1,
        in2   => APS2,
        ap    => atomics(0)
    );

    atc_1 : at_checker
    generic map (
        IN_1_WIDTH => APS1_WIDTH,
        IN_2_WIDTH => APS2_WIDTH,
        ADDR       => 1
    )
    port map(
        clk   => clk,
        rst_n => rst_n,
        config_addr  => config_addr(3-1 downto 0),
        config_data  => config_data,
        config_write => write1,
        in1   => APS1,
        in2   => APS2,
        ap    => atomics(1)
    );

end architecture;