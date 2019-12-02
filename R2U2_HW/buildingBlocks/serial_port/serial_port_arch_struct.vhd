----------------------------------------------------------------------------------
-- Company:      TU Wien - ECS Group                                            --
-- Engineer:     Thomas Polzer                                                  --
--                                                                              --
-- Create Date:  21.09.2010                                                     --
-- Design Name:  DIDELU                                                         --
-- Module Name:  serial_port_struct                                             --
-- Project Name: DIDELU                                                         --
-- Description:  Serial - Architecture                                          --
----------------------------------------------------------------------------------

----------------------------------------------------------------------------------
--                                LIBRARIES                                     --
----------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use work.serial_port_pkg.all;
use work.ram_pkg.all;
use work.sync_pkg.all;
use work.fifo_pkg.all;

----------------------------------------------------------------------------------
--                               ARCHITECTURE                                   --
----------------------------------------------------------------------------------

architecture struct of serial_port is
  signal rx_sync        : std_logic;
  signal tx_fifo_data   : std_logic_vector(7 downto 0);
  signal tx_fifo_ctrl_o : fifo_ctrl_out_type;
  signal tx_fifo_ctrl_i : fifo_ctrl_in_type;
  signal rx_fifo_data   : std_logic_vector(7 downto 0);
  signal rx_fifo_ctrl_o : fifo_ctrl_out_type;
  signal rx_fifo_ctrl_i : fifo_ctrl_in_type;
begin

  -- receiver instance
  receiver_inst : serial_port_receiver
    generic map
    (
      CLK_DIVISOR => CLK_FREQ / BAUD_RATE
      )
    port map
    (
      clk      => clk,
      res_n    => res_n,
      data     => rx_fifo_data,
      data_new => rx_fifo_ctrl_i.wr,
      rx       => rx_sync
      );

  -- transmitter instance
  transmitter_inst : serial_port_transmitter
    generic map
    (
      CLK_DIVISOR => CLK_FREQ / BAUD_RATE
      )
    port map
    (
      clk   => clk,
      res_n => res_n,
      data  => tx_fifo_data,
      empty => tx_fifo_ctrl_o.empty,
      rd    => tx_fifo_ctrl_i.rd,
      tx    => tx
      );

    tx_fifo_ctrl_i.wr <= tx_wr;

  -- tx fifo
  tx_fifo_inst : fifo
    generic map
    (
      MIN_DEPTH  => TX_FIFO_DEPTH,
      DATA_WIDTH => 8
      )
    port map
    (
      clk      => clk,
      res_n    => res_n,
      data_in  => tx_data,
      data_out => tx_fifo_data,
      ctrl_o   => tx_fifo_ctrl_o,
      ctrl_i   => tx_fifo_ctrl_i);

  tx_free <= not tx_fifo_ctrl_o.full;

  -- rx synchronizer
  sync_inst : sync
    generic map
    (
      SYNC_STAGES => SYNC_STAGES,
      RESET_VALUE => '1'
      )
    port map
    (
      clk      => clk,
      res_n    => res_n,
      data_in  => rx,
      data_out => rx_sync
      );

  -- rx fifo
  rx_fifo_inst : fifo
    generic map
    (
      MIN_DEPTH  => RX_FIFO_DEPTH,
      DATA_WIDTH => 8
      )
    port map
    (
      clk      => clk,
      res_n    => res_n,
      data_in  => rx_fifo_data,
      data_out => rx_data,
      ctrl_o   => rx_fifo_ctrl_o,
      ctrl_i   => rx_fifo_ctrl_i
      );
    
    rx_fifo_ctrl_i.rd <= rx_rd;
    rx_data_full <= rx_fifo_ctrl_o.full;
    rx_data_empty <= rx_fifo_ctrl_o.empty;

end architecture struct;

--- EOF ---
