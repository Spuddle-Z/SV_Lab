module spi_slave #(
    // Configuration parameters
    parameter DATA_WIDTH    = 8,           // Data width in bits (8, 16, 32)
    parameter FIFO_DEPTH    = 4,           // FIFO depth for buffering
    parameter CPOL          = 0,           // Clock polarity (0/1)
    parameter CPHA          = 0,           // Clock phase (0/1)
    parameter MSB_FIRST     = 1,           // 1 = MSB first, 0 = LSB first
    parameter DOUBLE_BUFFER = 1            // 1 = enable double buffering
)(
    // SPI Interface
    input  logic              sck_i,       // SPI clock input
    input  logic              cs_n_i,      // Chip select (active low)
    input  logic              mosi_i,      // Master out, slave in
    output logic              miso_o,      // Master in, slave out
    
    // Control Interface
    input  logic              clk_i,       // System clock
    input  logic              rst_n_i,     // Active-low reset
    
    // Data Interface
    input  logic [DATA_WIDTH-1:0] tx_data_i,     // Transmit data
    input  logic              tx_valid_i,        // Transmit data valid
    output logic              tx_ready_o,        // Transmit buffer ready
    
    output logic [DATA_WIDTH-1:0] rx_data_o,     // Received data
    output logic              rx_valid_o,        // Received data valid
    output logic              rx_ready_o,        // Receive buffer ready
    
    // Status Signals
    output logic              busy_o,            // Transfer in progress
    output logic              error_o,           // Error flag
    output logic [1:0]        error_code_o       // Error code (00: no error)
);

// ============================================================================
// Local Parameters and Types
// ============================================================================
localparam SHIFT_REG_WIDTH = DATA_WIDTH;
localparam COUNTER_WIDTH = $clog2(DATA_WIDTH);

typedef enum logic [1:0] {
    ERROR_NONE      = 2'b00,
    ERROR_OVERRUN   = 2'b01,
    ERROR_UNDERRUN  = 2'b10,
    ERROR_FRAME     = 2'b11
} error_type_t;

typedef enum logic [1:0] {
    STATE_IDLE      = 2'b00,
    STATE_ACTIVE    = 2'b01,
    STATE_COMPLETE  = 2'b10,
    STATE_ERROR     = 2'b11
} state_t;

// ============================================================================
// Internal Signals
// ============================================================================
logic [SHIFT_REG_WIDTH-1:0] shift_reg;      // Shift register
logic [COUNTER_WIDTH-1:0]   bit_counter;    // Bit counter
logic [DATA_WIDTH-1:0]      tx_buffer;      // Transmit buffer
logic [DATA_WIDTH-1:0]      rx_buffer;      // Receive buffer
logic                       tx_empty;       // Transmit buffer empty
logic                       rx_full;        // Receive buffer full
logic                       rx_valid_reg;   // Received data valid register
logic                       tx_valid_reg;   // Transmit data valid register
state_t                     current_state;  // Current state
state_t                     next_state;     // Next state
logic                       sck_sync;       // Synchronized SCK
logic                       sck_prev;       // Previous SCK value
logic                       sck_edge;       // SCK edge detection
logic                       cs_sync;        // Synchronized CS
logic                       cs_prev;        // Previous CS value
logic                       cs_falling;     // CS falling edge
logic                       cs_rising;      // CS rising edge
logic                       transfer_done;  // Transfer complete
logic [1:0]                 error_code;     // Error code register

// ============================================================================
// Clock and Chip Select Synchronization
// ============================================================================
// Synchronize asynchronous inputs to system clock domain
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        sck_sync <= CPOL;
        cs_sync  <= 1'b1;
        sck_prev <= CPOL;
        cs_prev  <= 1'b1;
    end else begin
        sck_sync <= sck_i;
        cs_sync  <= cs_n_i;
        sck_prev <= sck_sync;
        cs_prev  <= cs_sync;
    end
end

// Edge detection
assign sck_edge  = (sck_sync ^ sck_prev);
assign cs_falling = (cs_prev && !cs_sync);
assign cs_rising  = (!cs_prev && cs_sync);

// ============================================================================
// Clock Edge Detection Based on SPI Mode
// ============================================================================
logic sample_edge;
logic shift_edge;

generate
    if (CPHA == 0) begin : mode_cpha0
        // Mode 0 (CPOL=0, CPHA=0) and Mode 2 (CPOL=1, CPHA=0)
        // Sample on first edge, shift on second edge
        assign sample_edge = (CPOL == 0) ? (sck_sync && !sck_prev) : (!sck_sync && sck_prev);
        assign shift_edge  = (CPOL == 0) ? (!sck_sync && sck_prev) : (sck_sync && !sck_prev);
    end else begin : mode_cpha1
        // Mode 1 (CPOL=0, CPHA=1) and Mode 3 (CPOL=1, CPHA=1)
        // Shift on first edge, sample on second edge
        assign shift_edge  = (CPOL == 0) ? (sck_sync && !sck_prev) : (!sck_sync && sck_prev);
        assign sample_edge = (CPOL == 0) ? (!sck_sync && sck_prev) : (sck_sync && !sck_prev);
    end
endgenerate

// ============================================================================
// State Machine
// ============================================================================
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        current_state <= STATE_IDLE;
    end else begin
        current_state <= next_state;
    end
end

always_comb begin
    next_state = current_state;
    
    case (current_state)
        STATE_IDLE: begin
            if (cs_falling) begin
                next_state = STATE_ACTIVE;
            end
        end
        
        STATE_ACTIVE: begin
            if (cs_rising) begin
                next_state = STATE_COMPLETE;
            end else if (transfer_done) begin
                next_state = STATE_COMPLETE;
            end
        end
        
        STATE_COMPLETE: begin
            next_state = STATE_IDLE;
        end
        
        STATE_ERROR: begin
            if (cs_rising) begin
                next_state = STATE_IDLE;
            end
        end
        
        default: begin
            next_state = STATE_IDLE;
        end
    endcase
end

// ============================================================================
// Shift Register and Bit Counter
// ============================================================================
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        shift_reg <= '0;
        bit_counter <= '0;
        transfer_done <= 1'b0;
    end else begin
        case (current_state)
            STATE_IDLE: begin
                if (cs_falling) begin
                    // Load shift register with transmit data
                    if (DOUBLE_BUFFER && !tx_empty) begin
                        shift_reg <= tx_buffer;
                    end else begin
                        shift_reg <= '0;
                    end
                    bit_counter <= '0;
                    transfer_done <= 1'b0;
                end
            end
            
            STATE_ACTIVE: begin
                if (sample_edge && !cs_sync) begin
                    // Sample data on appropriate edge
                    if (MSB_FIRST) begin
                        shift_reg <= {shift_reg[SHIFT_REG_WIDTH-2:0], mosi_i};
                    end else begin
                        shift_reg <= {mosi_i, shift_reg[SHIFT_REG_WIDTH-1:1]};
                    end
                    
                    // Increment bit counter
                    if (bit_counter == DATA_WIDTH-1) begin
                        bit_counter <= '0;
                        transfer_done <= 1'b1;
                    end else begin
                        bit_counter <= bit_counter + 1;
                    end
                end
            end
            
            STATE_COMPLETE: begin
                transfer_done <= 1'b0;
            end
            
            default: begin
                // Do nothing
            end
        endcase
    end
end

// ============================================================================
// Transmit Data Path
// ============================================================================
generate
    if (DOUBLE_BUFFER) begin : double_buffer_enabled
        // Double buffering for better throughput
        always_ff @(posedge clk_i or negedge rst_n_i) begin
            if (!rst_n_i) begin
                tx_buffer <= '0;
                tx_empty <= 1'b1;
                tx_valid_reg <= 1'b0;
            end else begin
                if (tx_valid_i && tx_ready_o) begin
                    // Load new data into buffer
                    tx_buffer <= tx_data_i;
                    tx_empty <= 1'b0;
                    tx_valid_reg <= 1'b1;
                end else if (cs_falling && !tx_empty) begin
                    // Data transferred to shift register
                    tx_empty <= 1'b1;
                    tx_valid_reg <= 1'b0;
                end
            end
        end
        
        assign tx_ready_o = tx_empty;
        
    end else begin : single_buffer
        // Single buffer (direct connection)
        assign tx_buffer = tx_data_i;
        assign tx_valid_reg = tx_valid_i;
        assign tx_ready_o = !busy_o;
    end
endgenerate

// MISO output with tri-state control
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        miso_o <= 1'bz;
    end else begin
        if (cs_sync) begin
            // Chip select inactive, high impedance
            miso_o <= 1'bz;
        end else if (shift_edge) begin
            // Output data on appropriate edge
            if (MSB_FIRST) begin
                miso_o <= shift_reg[SHIFT_REG_WIDTH-1];
            end else begin
                miso_o <= shift_reg[0];
            end
        end
    end
end

// ============================================================================
// Receive Data Path
// ============================================================================
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        rx_buffer <= '0;
        rx_full <= 1'b0;
        rx_valid_reg <= 1'b0;
    end else begin
        if (transfer_done && !rx_full) begin
            // Store received data
            rx_buffer <= shift_reg;
            rx_full <= 1'b1;
            rx_valid_reg <= 1'b1;
        end else if (rx_ready_o && rx_full) begin
            // Data read by host
            rx_full <= 1'b0;
            rx_valid_reg <= 1'b0;
        end
    end
end

assign rx_data_o = rx_buffer;
assign rx_valid_o = rx_valid_reg;
assign rx_ready_o = !rx_full;

// ============================================================================
// Error Detection and Status Signals
// ============================================================================
always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
        error_code <= ERROR_NONE;
        error_o <= 1'b0;
    end else begin
        // Overrun error: new data received before previous data read
        if (transfer_done && rx_full) begin
            error_code <= ERROR_OVERRUN;
            error_o <= 1'b1;
        end
        // Underrun error: no data available for transmission
        else if (cs_falling && tx_empty) begin
            error_code <= ERROR_UNDERRUN;
            error_o <= 1'b1;
        end
        // Frame error: chip select deasserted before complete transfer
        else if (cs_rising && !transfer_done && current_state == STATE_ACTIVE) begin
            error_code <= ERROR_FRAME;
            error_o <= 1'b1;
        end
        // Clear error on chip select deassertion
        else if (cs_rising) begin
            error_o <= 1'b0;
        end
    end
end

assign error_code_o = error_code;
assign busy_o = (current_state != STATE_IDLE);

// ============================================================================
// Assertions for Design Verification
// ============================================================================
`ifdef SIMULATION
// Check that data width is power of 2 and within valid range
initial begin
    assert (DATA_WIDTH == 8 || DATA_WIDTH == 16 || DATA_WIDTH == 32) else
        $error("DATA_WIDTH must be 8, 16, or 32");
    
    assert (FIFO_DEPTH > 0) else
        $error("FIFO_DEPTH must be greater than 0");
    
    assert (CPOL == 0 || CPOL == 1) else
        $error("CPOL must be 0 or 1");
    
    assert (CPHA == 0 || CPHA == 1) else
        $error("CPHA must be 0 or 1");
end

// Check for setup/hold violations on MOSI
property mosi_setup_hold;
    @(posedge sample_edge) disable iff (cs_sync)
    $stable(mosi_i);
endproperty
assert property (mosi_setup_hold) else
    $error("MOSI setup/hold violation detected");

// Check for glitches on chip select during transfer
property cs_stable_during_transfer;
    @(posedge clk_i)
    (current_state == STATE_ACTIVE) |-> $stable(cs_sync);
endproperty
assert property (cs_stable_during_transfer) else
    $error("Chip select changed during active transfer");
`endif

endmodule
