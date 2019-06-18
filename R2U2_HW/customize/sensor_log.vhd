
-- Example of sensor_log
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.NUMERIC_STD.ALL;
use ieee.std_logic_unsigned.all;
use work.log_input_pkg.all;


entity sensor_log is
    Port ( 
        clk       : in  STD_LOGIC;
        reset     : in STD_LOGIC;
        pRBUS_DATA : in std_logic_vector(15 downto 0);
        pRBUS_ADDR : in std_logic_vector(7 downto 0);
        pRBUS_EN : in std_logic;
        data_update : out std_logic;
        test_data : out std_logic_vector(31 downto 0);
        log_data : out std_logic_vector(LOG_DATA_WIDTH-1 downto 0)
            );
end entity;

architecture Behavioral of sensor_log is

signal aps1_reg : std_logic_vector(18 downto 0);
signal aps2_reg : std_logic_vector(18 downto 0);
signal encoder_reg : std_logic_vector(31 downto 0);
signal pRBUS_ADDR_dly : std_logic_vector(7 downto 0);
signal pRBUS_EN_dly : std_logic;



begin
-- delay the signal for one clock cycle
signal_dly : process(clk, reset)
begin
    if(clk'event and clk = '1')then
        if(reset = '1')then
            pRBUS_ADDR_dly <= (others => '0');
            pRBUS_EN_dly <= '0';
            data_update <= '0';
        else
            pRBUS_ADDR_dly <= pRBUS_ADDR;
            pRBUS_EN_dly <= pRBUS_EN;
            data_update <= pRBUS_EN_dly;
        end if;
    end if;
end process;



data_listen : process(clk, reset)
begin
    if(clk'event and clk='1')then
        if(reset = '1')then
            aps1_reg <= (others => '0');
            aps2_reg <= (others => '0');
            encoder_reg <= (others => '0');
        else
            if(pRBUS_EN_dly = '1')then
                if(to_integer(unsigned(pRBUS_ADDR_dly))=0)then
                    aps1_reg(18 downto 16) <=  pRBUS_DATA(2 downto 0);
                elsif(to_integer(unsigned(pRBUS_ADDR_dly))=1)then
                    aps1_reg(15 downto 0) <=  pRBUS_DATA;
                elsif(to_integer(unsigned(pRBUS_ADDR_dly))=2)then
                    aps2_reg(18 downto 16) <=  pRBUS_DATA(2 downto 0);
                elsif(to_integer(unsigned(pRBUS_ADDR_dly))=3)then
                    aps2_reg(15 downto 0) <=  pRBUS_DATA;
                elsif(to_integer(unsigned(pRBUS_ADDR_dly))=0)then
                    encoder_reg(31 downto 16) <=  pRBUS_DATA;
                elsif(to_integer(unsigned(pRBUS_ADDR_dly))=1)then
                    encoder_reg(15 downto 0) <=  pRBUS_DATA;
                end if;

            end if;
        end if;
    end if;
end process;

log_hold : process(clk, reset)
begin
    if(clk'event and clk='1')then
        if(reset = '1')then
            log_data <=  (others => '0');
        else
            --log_data <=  aps1_reg & aps2_reg;
            test_data <= encoder_reg;
            log_data <= std_logic_vector(to_unsigned(6,aps1_reg'length))&std_logic_vector(to_unsigned(3,aps2_reg'length));
        end if;
    end if;
end process;


end Behavioral;

