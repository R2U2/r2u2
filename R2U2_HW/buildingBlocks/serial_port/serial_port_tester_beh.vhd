library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.serial_port_pkg.all;

architecture beh of serial_port_tester is
  signal data : std_logic_vector(7 downto 0);
  signal data_new : std_logic;

  function to_segs(value : in std_logic_vector(3 downto 0)) return std_logic_vector is
  begin
    case value is
      when x"0" => return "1000000";
      when x"1" => return "1111001";
      when x"2" => return "0100100";
      when x"3" => return "0110000";
      when x"4" => return "0011001";
      when x"5" => return "0010010";
      when x"6" => return "0000010";
      when x"7" => return "1111000";
      when x"8" => return "0000000";
      when x"9" => return "0010000";
      when x"A" => return "0001000";
      when x"B" => return "0000011";
      when x"C" => return "1000110";
      when x"D" => return "0100001";
      when x"E" => return "0000110";
      when x"F" => return "0001110";
      when others => return "1111111";
    end case;
  end function;
begin
  serial_port_inst : serial_port
    generic map
    (
      CLK_DIVISOR => 33330000 / 115200,
      SYNC_STAGES => 2
    )
    port map
    (
      sys_clk => sys_clk,
      sys_res_n => sys_res_n,
      tx_data => data,        -- Echo received characters
      tx_wr => data_new,      -- Echo received characters
      tx_free => open,
      tx_finished => open,
      rx_data => data,
      rx_data_new => data_new,
      rx => rx,
      tx => tx
    );

    segs_b <= to_segs(data(3 downto 0));
    segs_a <= to_segs(data(7 downto 4));
end architecture beh;
