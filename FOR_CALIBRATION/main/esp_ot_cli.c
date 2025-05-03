#include <stdio.h>
#include "driver/i2c.h"
#include "esp_log.h"
#include "esp_system.h"
#include "esp_err.h"
#include "esp_mac.h"
#include <math.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/adc.h"
#include "esp_adc/adc_oneshot.h"
#include "esp_adc/adc_cali.h"
#include "esp_adc/adc_cali_scheme.h"
#include "openthread/thread.h"
#include "portmacro.h"
#include "freertos/semphr.h"
#include <string.h>
#include "sdkconfig.h"
#include "esp_event.h"
#include "esp_netif.h"
#include "esp_openthread.h"
#include "esp_openthread_cli.h"
#include "esp_openthread_lock.h"
#include "esp_openthread_netif_glue.h"
#include "esp_openthread_types.h"
#include "esp_ot_config.h"
#include "esp_vfs_eventfd.h"
#include "nvs_flash.h"
#include "driver/gpio.h"
#include "openthread/cli.h"
#include "openthread/instance.h"
#include "openthread/thread_ftd.h"
#include "openthread/link.h"
#include "openthread/netdata.h"
#include "openthread/udp.h"
#include "led_strip.h"
#include "openthread/coap.h"
#include <sys/time.h>    // For time functions
#include <time.h>        // For time functions
SemaphoreHandle_t i2c_mutex;

//---------------------- Global Variables for DS3231 RTC -----------------------
// Hardcoded Unix time (as string) to set the RTC (e.g., "1700000000")
const char *g_hardcoded_unix_time_str = "1700000000";
// Global variable to hold the current RTC time in Unix seconds as a string.
char g_synced_time_str[64] = {0};
// DS3231 I2C definitions
#define DS3231_ADDR     0x68
#define DS3231_REG_TIME 0x00

// I2C configuration for DS3231
#define DS3231_I2C_PORT       I2C_NUM_1
#define DS3231_I2C_SDA_IO     12
#define DS3231_I2C_SCL_IO     22
#define DS3231_I2C_FREQ_HZ    100000


//SEN-55
#define I2C_NUM I2C_NUM_0
#define I2C_SCL 10
#define I2C_SDA 11
#define I2C_FREQ_HZ 100000
#define SEN55_I2C_ADDRESS 0x69

//SCD-41
#define I2C_SCD41_NUM I2C_NUM_0              
#define I2C_SCD41_SCL 10     // GPIO number for I2C SCL (use GPIO 10)
#define I2C_SCD41_SDA 11     // GPIO number for I2C SDA (use GPIO 11)
#define I2C_SCD41_FREQ_HZ 100000             
#define I2C_SCD41_TX_BUF_DISABLE 0           
#define I2C_SCD41_RX_BUF_DISABLE 0          

#define SCD41_I2C_ADDRESS 0x62               // Default I2C address for SCD41 from datasheet
#define SCD41_SERIAL_NUMBER_CMD 0x3682       // Command to read serial number
#define SCD41_START_PERIODIC_MEASUREMENT_CMD 0x21B1  // Command to start periodic measurement
#define SCD41_READ_MEASUREMENT_CMD 0xEC05    // Command to read measurement data
#define SCD41_STOP_PERIODIC_MEASUREMENT_CMD 0x3F86  // Command to stop periodic measurement
#define SCD41_SINGLE_SHOT_MEASUREMENT_CMD   0x219D  // Command for single shot measurement
#define SCD41_START_LOW_POWER_PERIODIC_MEASUREMENT_CMD 0x21AC  // Low power periodic measurement command

#define SCD41_SET_ASC_CMD 0x2416
#define SCD41_GET_ASC_CMD 0x2313


//MiCS-4514
#define ADC1_CH1_RED ADC_CHANNEL_0  // GPIO1 (ADC1_CH0)
#define ADC1_CH2_NOX ADC_CHANNEL_1  // GPIO2 (ADC1_CH1)
static adc_oneshot_unit_handle_t adc1_handle = NULL;
static adc_cali_handle_t adc1_cali_handle = NULL;

#define ADC_RAW_MIN_MICS 1800  // Typical raw value for 0V (depends on ESP32 variant)
#define ADC_RAW_MAX_MICS 4095  // Max ADC value
#define ADC_VOLTAGE_MAX_MICS 2200  // 2.2V max for 11 dB attenuation

double R0_co = 243123; // CHANGE THIS FOR EVERY NODE!!!
double R0_no2 = 13598; // CHANGE THIS FOR EVERY NODE!!!


//ULPSM-SO2
#define ADC_CHANNEL_VGAS   ADC_CHANNEL_3 // GPIO4 (ADC1_CH3)
#define ADC_CHANNEL_VREF   ADC_CHANNEL_2 // GPIO3 (ADC1_CH2)
#define SENSOR_MAX_OUTPUT  3000.0 // Maximum output voltage in mV (3.0V)
#define SENSOR_MAX_PPM     20.0   // Maximum measurable SO2 concentration in ppm
// Sampling parameters
#define SAMPLES_PER_INTERVAL  60    // 60 readings, one per second
#define OVERSAMPLE_COUNT      16    // number of ADC reads to average per sample
float so2_ppm;
float sensitivity = 46.11; // CHANGE THIS FOR EVERY NODE!!!
float gain = 100; // CHANGE THIS FOR EVERY NODE!!!
float offset = 326; // CHANGE THIS FOR EVERY NODE!!!

// LONGITUDE AND LATITUDE CONSTANTS (Comment when not in use)

//float longi=121.068661, lat=14.652522; // AQ1
float longi=121.068525, lat=14.652522; // AQ2
//float longi=121.068514, lat=14.652406; // AQ3
//float longi=121.068667, lat=14.6524; // AQ4

//static const char *TAG = "AQ NODE 1";
static const char *TAG = "AQ NODE 2";
//static const char *TAG = "AQ NODE 3";
//static const char *TAG = "AQ NODE 4";

static led_strip_handle_t led_strip;
char payloadd[500];  // Global pointer
float pm10=0.0,pm25=0.0,co2=0.0,no2=0.0,co=0.0, so2=0.0;
int connected=0;
int time_established=0;
int data_ready=0;

static SemaphoreHandle_t server_check_sem = NULL;
static bool server_reachable = false;

static otInstance *instance = NULL;

char global_mac_str[18] = {0};

// Global variable to hold the "hardcoded" time value (Unix timestamp in seconds).
// Initially set to January 1, 2025, 00:00:00 UTC.
long long global_sync_time;

//---------------------- DS3231 Helper Functions -----------------------
// Convert BCD to Decimal
static inline uint8_t bcd_to_dec(uint8_t val) {
    return ((val >> 4) * 10) + (val & 0x0F);
}

// Convert Decimal to BCD
static inline uint8_t dec_to_bcd(uint8_t val) {
    return ((val / 10) << 4) | (val % 10);
}

// Initialize I2C Master for DS3231
static esp_err_t ds3231_i2c_master_init(void) {
    i2c_config_t conf = {
        .mode = I2C_MODE_MASTER,
        .sda_io_num = DS3231_I2C_SDA_IO,
        .sda_pullup_en = GPIO_PULLUP_ENABLE,
        .scl_io_num = DS3231_I2C_SCL_IO,
        .scl_pullup_en = GPIO_PULLUP_ENABLE,
        .master.clk_speed = DS3231_I2C_FREQ_HZ,
    };
    esp_err_t err = i2c_param_config(DS3231_I2C_PORT, &conf);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "DS3231 I2C config error: %s", esp_err_to_name(err));
        return err;
    }
    err = i2c_driver_install(DS3231_I2C_PORT, conf.mode, 0, 0, 0);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "DS3231 I2C install error: %s", esp_err_to_name(err));
    }
    return err;
}

// Set time in DS3231 using struct tm.
static esp_err_t ds3231_set_time(struct tm *timeinfo) {
    uint8_t data[7];
    data[0] = dec_to_bcd(timeinfo->tm_sec);
    data[1] = dec_to_bcd(timeinfo->tm_min);
    data[2] = dec_to_bcd(timeinfo->tm_hour);  // 24-hour mode assumed
    // DS3231 expects day-of-week as 1-7. tm_wday is 0-6 (Sunday==0), so adjust (e.g., Sunday becomes 7).
    data[3] = dec_to_bcd((timeinfo->tm_wday == 0) ? 7 : timeinfo->tm_wday);
    data[4] = dec_to_bcd(timeinfo->tm_mday);
    data[5] = dec_to_bcd(timeinfo->tm_mon + 1);
    data[6] = dec_to_bcd(timeinfo->tm_year - 100);

    i2c_cmd_handle_t cmd = i2c_cmd_link_create();
    i2c_master_start(cmd);
    i2c_master_write_byte(cmd, (DS3231_ADDR << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write_byte(cmd, DS3231_REG_TIME, true);
    i2c_master_write(cmd, data, sizeof(data), true);
    i2c_master_stop(cmd);
    esp_err_t err = i2c_master_cmd_begin(DS3231_I2C_PORT, cmd, pdMS_TO_TICKS(1000));
    i2c_cmd_link_delete(cmd);
    return err;
}

// Read time from DS3231 into struct tm.
static esp_err_t ds3231_get_time(struct tm *timeinfo) {
    uint8_t data[7] = {0};

    // Set register pointer to 0x00
    i2c_cmd_handle_t cmd = i2c_cmd_link_create();
    i2c_master_start(cmd);
    i2c_master_write_byte(cmd, (DS3231_ADDR << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write_byte(cmd, DS3231_REG_TIME, true);
    i2c_master_stop(cmd);
    esp_err_t err = i2c_master_cmd_begin(DS3231_I2C_PORT, cmd, pdMS_TO_TICKS(1000));
    i2c_cmd_link_delete(cmd);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Error setting DS3231 pointer: %s", esp_err_to_name(err));
        return err;
    }

    // Read 7 bytes from DS3231 registers
    cmd = i2c_cmd_link_create();
    i2c_master_start(cmd);
    i2c_master_write_byte(cmd, (DS3231_ADDR << 1) | I2C_MASTER_READ, true);
    i2c_master_read(cmd, data, 6, I2C_MASTER_ACK);
    i2c_master_read_byte(cmd, &data[6], I2C_MASTER_NACK);
    i2c_master_stop(cmd);
    err = i2c_master_cmd_begin(DS3231_I2C_PORT, cmd, pdMS_TO_TICKS(1000));
    i2c_cmd_link_delete(cmd);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "Error reading DS3231 data: %s", esp_err_to_name(err));
        return err;
    }

    // Convert the BCD values to binary and populate struct tm
    timeinfo->tm_sec  = bcd_to_dec(data[0] & 0x7F);
    timeinfo->tm_min  = bcd_to_dec(data[1]);
    timeinfo->tm_hour = bcd_to_dec(data[2] & 0x3F);
    timeinfo->tm_wday = bcd_to_dec(data[3]) - 1;
    timeinfo->tm_mday = bcd_to_dec(data[4]);
    timeinfo->tm_mon  = bcd_to_dec(data[5]) - 1;
    timeinfo->tm_year = bcd_to_dec(data[6]) + 100; // tm_year: years since 1900
    timeinfo->tm_isdst = 0;
    return ESP_OK;
}


static void update_global_mac_string(void)
{
    uint8_t mac_addr[6] = {0};
    esp_err_t err = esp_efuse_mac_get_default(mac_addr);
    if (err == ESP_OK) {
        // Format the MAC address into the global variable.
        snprintf(global_mac_str, sizeof(global_mac_str), "%02X:%02X:%02X:%02X:%02X:%02X",
                 mac_addr[0], mac_addr[1], mac_addr[2],
                 mac_addr[3], mac_addr[4], mac_addr[5]);
    } else {
        snprintf(global_mac_str, sizeof(global_mac_str), "N/A");
        ESP_LOGE(TAG, "Failed to read MAC address: %s", esp_err_to_name(err));
    }
}


//FOR THREAD CONNECTION
static void configure_led(void)
{
    //ESP_LOGI(TAG, "Example configured to blink addressable LED!");
    /* LED strip initialization with the GPIO and pixels number*/
    led_strip_config_t strip_config = {
        .strip_gpio_num = 8,
        .max_leds = 1, // at least one LED on board
    };

    led_strip_rmt_config_t rmt_config = {
        .resolution_hz = 10 * 1000 * 1000, // 10MHz
        .flags.with_dma = false,
    };
    ESP_ERROR_CHECK(led_strip_new_rmt_device(&strip_config, &rmt_config, &led_strip));

    led_strip_spi_config_t spi_config = {
        .spi_bus = SPI2_HOST,
        .flags.with_dma = true,
    };
    ESP_ERROR_CHECK(led_strip_new_spi_device(&strip_config, &spi_config, &led_strip));
}
static void update_led_status(otDeviceRole role) {
    if (role == OT_DEVICE_ROLE_CHILD || role == OT_DEVICE_ROLE_ROUTER) {
        led_strip_set_pixel(led_strip, 0, 10, 10, 0);
        led_strip_refresh(led_strip);
    }
    else if( role == OT_DEVICE_ROLE_LEADER){
		led_strip_set_pixel(led_strip, 0, 0, 0, 10);
        led_strip_refresh(led_strip);
	}	
    else {
        led_strip_set_pixel(led_strip, 0, 10, 0, 0);
        led_strip_refresh(led_strip);
    }
}
static void configure_for_joining(otInstance *instance)
{
    otOperationalDataset dataset;
    memset(&dataset, 0, sizeof(dataset));

    dataset.mActiveTimestamp.mSeconds = 1;
    dataset.mActiveTimestamp.mTicks = 0;
    dataset.mActiveTimestamp.mAuthoritative = false;
    dataset.mComponents.mIsActiveTimestampPresent = true;

    dataset.mChannel = 15;
    dataset.mComponents.mIsChannelPresent = true;

    dataset.mPanId = 0x2222;
    dataset.mComponents.mIsPanIdPresent = true;

    memcpy(dataset.mExtendedPanId.m8, "C0DE1AB5C0DE1AB5", sizeof(dataset.mExtendedPanId));
    dataset.mComponents.mIsExtendedPanIdPresent = true;

    memcpy(dataset.mNetworkKey.m8, "1234C0DE1AB51234C0DE1AB51234C0DE", sizeof(dataset.mNetworkKey));
    dataset.mComponents.mIsNetworkKeyPresent = true;

    strncpy(dataset.mNetworkName.m8, "ESPThread", sizeof(dataset.mNetworkName.m8));
    dataset.mComponents.mIsNetworkNamePresent = true;

    otError error = otDatasetSetActive(instance, &dataset);
    if (error == OT_ERROR_NONE)
         ESP_LOGI(TAG, "Network configuration applied successfully");
    else
         ESP_LOGE(TAG, "Failed to configure network: %s", otThreadErrorToString(error));
}
// Function to enable and join the Thread network
static void join_thread_network(otInstance *instance) {
    configure_for_joining(instance);

    otError error = otThreadSetEnabled(instance, true);
    if (error == OT_ERROR_NONE) {
        ESP_LOGI(TAG, "Thread protocol enabled. Attempting to join the network...");
    } else {
        ESP_LOGE(TAG, "Failed to enable Thread protocol: %s", otThreadErrorToString(error));
        abort();
    }
}



static void server_check_response_handler(void *aContext, otMessage *aMessage,
                                            const otMessageInfo *aMessageInfo, otError aResult)
{
    if (aResult == OT_ERROR_NONE)
    {
		 otCoapCode responseCode = otCoapMessageGetCode(aMessage);
		 char payload[128] = {0};
         uint16_t offset = otMessageGetOffset(aMessage);
         uint16_t payloadLength = otMessageGetLength(aMessage) - offset;
         if (payloadLength < sizeof(payload))
         {
             int bytesRead = otMessageRead(aMessage, offset, payload, payloadLength);
             if (bytesRead > 0)
             {
                 payload[bytesRead] = '\0';
                 ESP_LOGI(TAG, "Response Payload: %s", payload);
             }
         }
		 
		 if(responseCode == OT_COAP_CODE_CONTENT){
			 ESP_LOGI(TAG, "Server check: Received response");
         	 server_reachable = true;
		 }
		 else{
			 
			 //ESP_LOGE(TAG, "Server check: Response error: %s", otThreadErrorToString(aResult));
         	 //server_reachable = false;
		 }
		 
		
         
    }
    else
    {
         ESP_LOGE(TAG, "Server check: Response error: %s", otThreadErrorToString(aResult));
         server_reachable = false;
    }
    xSemaphoreGive(server_check_sem);
}

static bool check_server_status(otInstance *instance)
{
    server_reachable = false;
    if (server_check_sem == NULL)
    {
         server_check_sem = xSemaphoreCreateBinary();
    }
    else
    {
         /* Reset the semaphore in case a previous check is still pending */
         xSemaphoreTake(server_check_sem, 0);
    }

    otError error;
    otMessage *message = otCoapNewMessage(instance, NULL);
    if (message == NULL)
    {
         ESP_LOGE(TAG, "Failed to allocate CoAP message for server check");
         return false;
    }

    /* Initialize as a GET request */
    otCoapMessageInit(message, OT_COAP_TYPE_CONFIRMABLE, OT_COAP_CODE_GET);
    otCoapMessageGenerateToken(message, OT_COAP_DEFAULT_TOKEN_LENGTH);

    /* Append URI path "status" (server should respond to this) */
    error = otCoapMessageAppendUriPathOptions(message, "api/status");
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to append URI path for server check: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return false;
    }

    /* Prepare destination address and port (update with your server's IPv6 address) */
    otMessageInfo messageInfo;
    memset(&messageInfo, 0, sizeof(messageInfo));
    otIp6Address destAddress;
    error = otIp6AddressFromString("2001:0db8:85a3::1", &destAddress);
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to parse server IPv6 address for server check: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return false;
    }
    messageInfo.mPeerAddr = destAddress;
    messageInfo.mPeerPort = OT_DEFAULT_COAP_PORT;

    ESP_LOGI(TAG, "Checking server availability...");
    error = otCoapSendRequest(instance, message, &messageInfo, server_check_response_handler, NULL);
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to send server check request: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return false;
    }

    /* Wait for response with a timeout (e.g., 2000 ms) */
    if (xSemaphoreTake(server_check_sem, pdMS_TO_TICKS(2000)) == pdTRUE)
    {
         return server_reachable;
    }
    else
    {
         ESP_LOGE(TAG, "Server check timed out");
         return false;
    }
}

static void coap_response_handler(void *aContext, otMessage *aMessage,
                                  const otMessageInfo *aMessageInfo, otError aResult)
{
    if (aResult == OT_ERROR_NONE)
    {
         ESP_LOGI(TAG, "CoAP Client: Received response");
         char payload[128] = {0};
         uint16_t offset = otMessageGetOffset(aMessage);
         uint16_t payloadLength = otMessageGetLength(aMessage) - offset;
         if (payloadLength < sizeof(payload))
         {
             int bytesRead = otMessageRead(aMessage, offset, payload, payloadLength);
             if (bytesRead > 0)
             {
                 payload[bytesRead] = '\0';
                 ESP_LOGI(TAG, "Response Payload: %s", payload);
             }
         }
    }
    else
    {
         ESP_LOGE(TAG, "CoAP Client: Response error: %s", otThreadErrorToString(aResult));
    }
}

static void send_coap_post_request(otInstance *instance)
{
    otError error;
    otMessage *message = otCoapNewMessage(instance, NULL);
    if (message == NULL)
    {
         ESP_LOGE(TAG, "Failed to allocate CoAP message");
         return;
    }

    /* Initialize as a POST request */
    otCoapMessageInit(message, OT_COAP_TYPE_CONFIRMABLE, OT_COAP_CODE_POST);
    otCoapMessageGenerateToken(message, OT_COAP_DEFAULT_TOKEN_LENGTH);

    /* Append URI path "sensor/data" */
    error = otCoapMessageAppendUriPathOptions(message, "api/sensor-data");
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to append URI path options: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return;
    }

    /* Set the payload marker and append the payload "Hello. THIS IS FROM NODE 1" */
    error = otCoapMessageSetPayloadMarker(message);
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to set payload marker: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return;
    }
    const char *payload = payloadd;
    error = otMessageAppend(message, payload, strlen(payload));
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to append payload: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return;
    }

    /* Prepare the destination address and port (update with your server's IPv6 address) */
    otMessageInfo messageInfo;
    memset(&messageInfo, 0, sizeof(messageInfo));
    otIp6Address destAddress;
    error = otIp6AddressFromString("fdde:ad00:beef:0:c943:8315:7641:75a9", &destAddress);
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to parse server IPv6 address: %s", otThreadErrorToString(error));
         otMessageFree(message);
         return;
    }
    messageInfo.mPeerAddr = destAddress;
    messageInfo.mPeerPort = OT_DEFAULT_COAP_PORT;

    ESP_LOGI(TAG, "Sending CoAP POST request with payload: %s", payload);
    error = otCoapSendRequest(instance, message, &messageInfo, coap_response_handler, NULL);
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to send CoAP POST request: %s", otThreadErrorToString(error));
         otMessageFree(message);
    }
}

static void datetime_response_handler(void *aContext, otMessage *aMessage,
                                        const otMessageInfo *aMessageInfo, otError aResult)
{
    if (aResult == OT_ERROR_NONE && aMessage != NULL)
    {
        char payloadtime[64] = {0};
        int length = otMessageRead(aMessage, otMessageGetOffset(aMessage), payloadtime, sizeof(payloadtime) - 1);
        if (length > 0)
        {
            payloadtime[length] = '\0';
            ESP_LOGI(TAG, "Received datetime: %s", payloadtime);
            // Set DS3231 time using a hardcoded Unix timestamp global variable.
		    time_t hardcoded_unix = (time_t)atoll(payloadtime);
		    //ESP_LOGI(TAG, "Hardcoded Unix time: %lld", hardcoded_unix);
		    struct tm rtc_set_time;
		    memset(&rtc_set_time, 0, sizeof(rtc_set_time));
			// Use localtime_r to convert Unix time to struct tm (adjust to local time as needed)
		    if (localtime_r(&hardcoded_unix, &rtc_set_time) == NULL) {
		        ESP_LOGE(TAG, "Error converting hardcoded Unix time");
		    }
		    // Set the DS3231 with the time
		    if (ds3231_set_time(&rtc_set_time) == ESP_OK) {
		        ESP_LOGI(TAG, "DS3231 time set successfully from hardcoded Unix string");
		        time_established=1;
		    } else {
		        ESP_LOGE(TAG, "Failed to set DS3231 time");
		    }
		            }
    }
    else
    {
        ESP_LOGE(TAG, "Error in response: %s", otThreadErrorToString(aResult));
    }
}

static void send_datetime_get_request(otInstance *aInstance)
{
    otMessage *message = otCoapNewMessage(aInstance, NULL);
    if (message == NULL)
    {
        ESP_LOGE(TAG, "Failed to allocate CoAP message");
        return;
    }

    otCoapMessageInit(message, OT_COAP_TYPE_CONFIRMABLE, OT_COAP_CODE_GET);
    otCoapMessageGenerateToken(message, OT_COAP_DEFAULT_TOKEN_LENGTH);
    
    

    // Append the URI path option. Here we use "api/datetime".
    otError error = otCoapMessageAppendUriPathOptions(message, "api/datetime");
    if (error != OT_ERROR_NONE)
    {
        otMessageFree(message);
        ESP_LOGE(TAG, "Error appending URI path: %s", otThreadErrorToString(error));
        return;
    }

    // Set up the destination info.
    otMessageInfo messageInfo;
    memset(&messageInfo, 0, sizeof(messageInfo));
    // Set destination address – change "fd00::1" to your server's IPv6 address.
    error=  otIp6AddressFromString("2001:0db8:85a3::1", &messageInfo.mPeerAddr);
    messageInfo.mPeerPort = OT_DEFAULT_COAP_PORT;

    // Send the GET request and register the response handler.
    error = otCoapSendRequest(aInstance, message, &messageInfo, datetime_response_handler, NULL);
    if (error != OT_ERROR_NONE)
    {
        otMessageFree(message);
        ESP_LOGE(TAG, "Error sending GET request: %s", otThreadErrorToString(error));
    }
    else
    {
        ESP_LOGI(TAG, "Sent GET request for datetime");
    }
}

static void set_datetime_manual(otInstance *aInstance){
	// Set DS3231 time using a hardcoded Unix timestamp global variable.
    time_t hardcoded_unix = (time_t)atoll(g_hardcoded_unix_time_str);
    ESP_LOGI(TAG, "Hardcoded Unix time: %lld", hardcoded_unix);
    struct tm rtc_set_time;
    memset(&rtc_set_time, 0, sizeof(rtc_set_time));
    // Use localtime_r to convert Unix time to struct tm (adjust to local time as needed)
    if (localtime_r(&hardcoded_unix, &rtc_set_time) == NULL) {
        ESP_LOGE(TAG, "Error converting hardcoded Unix time");
    }
    // Set the DS3231 with the time
    if (ds3231_set_time(&rtc_set_time) == ESP_OK) {
        ESP_LOGI(TAG, "DS3231 time set successfully from hardcoded Unix string");
        time_established=1;
    } else {
        ESP_LOGE(TAG, "Failed to set DS3231 time");
    }
}

static void coap_client_task(void *arg)
{
    otInstance *instance = (otInstance *)arg;
    /* Wait for network stabilization before sending requests */
    vTaskDelay(pdMS_TO_TICKS(5000));
    //send_datetime_get_request(instance);
    set_datetime_manual(instance);
    vTaskDelay(pdMS_TO_TICKS(5000));
    vTaskDelay(pdMS_TO_TICKS(2000));
    while (true)
    {
         // First, check if the server is reachable
         if (data_ready==1)
         {
              //ESP_LOGI(TAG, "Server is reachable. Proceeding with POST request.");
              send_coap_post_request(instance);
              vTaskDelay(pdMS_TO_TICKS(5000)); // sampling time
         }
         else
         {
              //ESP_LOGW(TAG, "Server not reachable, Trying to connect to the server...");
         }
         vTaskDelay(pdMS_TO_TICKS(1000));
    }
}
static void ot_state_monitor_task(void *arg) {
    otInstance *instance = (otInstance *)arg;

    while (true) {
        otDeviceRole role = otThreadGetDeviceRole(instance);
        const char *role_str = (role == OT_DEVICE_ROLE_DISABLED) ? "Disabled" :
                               (role == OT_DEVICE_ROLE_DETACHED) ? "Detached" :
                               (role == OT_DEVICE_ROLE_CHILD) ? "Child" :
                               (role == OT_DEVICE_ROLE_ROUTER) ? "Router" :
                               (role == OT_DEVICE_ROLE_LEADER) ? "Leader" : "Unknown";
        //ESP_LOGI(TAG, "Current Thread role: %s", role_str);

        // Update LED status based on network role
        //print_ipv6_addresses(instance);
        update_led_status(role);

        // Log neighbor information
        otNeighborInfoIterator iterator = OT_NEIGHBOR_INFO_ITERATOR_INIT;
        otNeighborInfo neighbor_info;

        while (otThreadGetNextNeighborInfo(instance, &iterator, &neighbor_info) == OT_ERROR_NONE) {
            /*ESP_LOGI(TAG, "Neighbor: ExtAddr: %02x%02x%02x%02x%02x%02x%02x%02x, RLOC16: 0x%04x, Link Quality: %d",
                     neighbor_info.mExtAddress.m8[0], neighbor_info.mExtAddress.m8[1],
                     neighbor_info.mExtAddress.m8[2], neighbor_info.mExtAddress.m8[3],
                     neighbor_info.mExtAddress.m8[4], neighbor_info.mExtAddress.m8[5],
                     neighbor_info.mExtAddress.m8[6], neighbor_info.mExtAddress.m8[7],
                     neighbor_info.mRloc16, neighbor_info.mLinkQualityIn);*/
        }
        if (role!=OT_DEVICE_ROLE_DETACHED){
			//ESP_LOGI(TAG, "Connected to the Thread Network Successfully!");
			if (connected==0){
				/* Start the CoAP service (required for receiving responses) */
			    otError error = otCoapStart(instance, OT_DEFAULT_COAP_PORT);
			    if (error != OT_ERROR_NONE)
			         ESP_LOGE(TAG, "Failed to start CoAP service: %s", otThreadErrorToString(error));
			    else
			         ESP_LOGI(TAG, "CoAP service started successfully");
			
			
			    /* Create the CoAP client task to check server status and send POST requests periodically */
			    xTaskCreate(coap_client_task, "coap_client_task", 10240, instance, 5, NULL);
			    connected=1;
			}
		

		}
		else{
			connected=0;
		}

        vTaskDelay(pdMS_TO_TICKS(10000)); // Wait 10 seconds before checking again
    }
}
static void ot_task_worker(void *aContext)
{
    esp_openthread_platform_config_t config = {
         .radio_config = ESP_OPENTHREAD_DEFAULT_RADIO_CONFIG(),
         .host_config = ESP_OPENTHREAD_DEFAULT_HOST_CONFIG(),
         .port_config = ESP_OPENTHREAD_DEFAULT_PORT_CONFIG(),
    };
    ESP_LOGI(TAG, "Initializing OpenThread stack...");
    ESP_ERROR_CHECK(esp_openthread_init(&config));

    instance = esp_openthread_get_instance();
    
    //Set transmitter power to 10dBm
    otError txError = otPlatRadioSetTransmitPower(instance, 10);
    if (txError != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to set TX power: %s", otThreadErrorToString(txError));
    }
    else
    {
         ESP_LOGI(TAG, "TX power set to 10 dBm");
    }

    /* Enable IPv6 */
    otError error = otIp6SetEnabled(instance, true);
    if (error != OT_ERROR_NONE)
    {
         ESP_LOGE(TAG, "Failed to enable IPv6: %s", otThreadErrorToString(error));
         abort();
    }
    ESP_LOGI(TAG, "IPv6 enabled");

    /* Automatically join (or create) the Thread network */
    join_thread_network(instance);
    vTaskDelay(pdMS_TO_TICKS(10000)); // Allow time for network join
    /* Optional: Create a state monitor task to log the Thread role */
    xTaskCreate(ot_state_monitor_task, "ot_state_monitor_task", 4096, instance, 5, NULL);


    /* Launch the OpenThread main loop (this call blocks) */
    esp_openthread_launch_mainloop();
    esp_openthread_netif_glue_deinit();
    vTaskDelete(NULL);
}




// CRC-8 function for SEN55
uint8_t calculate_crc8(uint8_t data[2]) {
    uint8_t crc = 0xFF;
    for (int i = 0; i < 2; i++) {
        crc ^= data[i];
        for (uint8_t bit = 8; bit > 0; --bit) {
            if (crc & 0x80) {
                crc = (crc << 1) ^ 0x31u;
            } else {
                crc = (crc << 1);
            }
        }
    }
    return crc;
}

esp_err_t i2c_master_init(i2c_port_t i2c_num, gpio_num_t sda, gpio_num_t scl, uint32_t freq) {
    i2c_config_t conf = {
        .mode = I2C_MODE_MASTER,
        .sda_io_num = sda,
        .scl_io_num = scl,
        .sda_pullup_en = GPIO_PULLUP_ENABLE,
        .scl_pullup_en = GPIO_PULLUP_ENABLE,
        .master.clk_speed = freq,
    };
    ESP_ERROR_CHECK(i2c_param_config(i2c_num, &conf));
    return i2c_driver_install(i2c_num, conf.mode, 0, 0, 0);
}

esp_err_t start_measurement_sen55() {
    uint8_t cmd[] = {0x00, 0x21};
    esp_err_t ret = i2c_master_write_to_device(I2C_NUM, SEN55_I2C_ADDRESS, cmd, sizeof(cmd), pdMS_TO_TICKS(1000));
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SEN 55] Failed to start measurement: %s", esp_err_to_name(ret));
        return ret;
    }
    ESP_LOGI(TAG, "[SEN 55] Measurement started successfully.");
    vTaskDelay(pdMS_TO_TICKS(500)); // Ensure the sensor transitions to measurement mode
    return ESP_OK;
}

esp_err_t check_data_ready_flag() {
    uint8_t cmd[] = {0x02, 0x02};
    uint8_t data[3];
    esp_err_t ret;

    ret = i2c_master_write_to_device(I2C_NUM, SEN55_I2C_ADDRESS, cmd, sizeof(cmd), pdMS_TO_TICKS(1000));
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SEN 55] Failed to send data-ready flag command: %s", esp_err_to_name(ret));
        return ret;
    }

    vTaskDelay(pdMS_TO_TICKS(10)); // Short delay before reading

    ret = i2c_master_read_from_device(I2C_NUM, SEN55_I2C_ADDRESS, data, sizeof(data), pdMS_TO_TICKS(1000));
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SEN 55] Failed to read data-ready flag response: %s", esp_err_to_name(ret));
        return ret;
    }

    if (data[1] == 0x01) {
        ESP_LOGI(TAG, "[SEN 55] Data is ready.");
        return 1;
    } else {
        ESP_LOGW(TAG, "[SEN 55] No new data available.");
        return ESP_ERR_INVALID_STATE;
    }
}

void read_measured_values_sen55() {
    uint8_t cmd[] = {0x03, 0xC4};
    uint8_t data[24];
    esp_err_t ret;

    ret = i2c_master_write_to_device(I2C_NUM, SEN55_I2C_ADDRESS, cmd, sizeof(cmd), pdMS_TO_TICKS(1000));
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SEN 55] Failed to send measured values command: %s", esp_err_to_name(ret));
        //return ret;
    }

    vTaskDelay(pdMS_TO_TICKS(20)); // Slight delay before reading data

    ret = i2c_master_read_from_device(I2C_NUM, SEN55_I2C_ADDRESS, data, sizeof(data), pdMS_TO_TICKS(1000));
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SEN 55] Failed to read measured values: %s", esp_err_to_name(ret));
        //return ret;
    }

    // Parse PM2.5 value (bytes 3, 4) and its CRC (byte 5)
    uint16_t pm25_raw = data[3] << 8; 
    pm25_raw |= data[4];
    uint8_t pm25_crc = data[5];
    if (pm25_crc != calculate_crc8(&data[3])) {
        ESP_LOGE(TAG, "PM2.5 CRC mismatch! Expected: 0x%02X, Received: 0x%02X", calculate_crc8(&data[3]), pm25_crc);
        //return ESP_ERR_INVALID_CRC;
    }
    else{
		//ESP_LOGI(TAG, "PM2.5 CRC Correct!");

	}
    //pm25 = pm25_raw / 10.0; // Scale factor is 10
    //pm25 = 1.9467002394827233*pm25 + (2.5926092705655464);

    // Parse PM10 value (bytes 9, 10) and its CRC (byte 11)
    uint16_t pm10_raw = data[9] << 8; 
    pm10_raw |= data[10];
    uint8_t pm10_crc = data[11];
    if (pm10_crc != calculate_crc8(&data[9])) {
        ESP_LOGE(TAG, "PM10 CRC mismatch! Expected: 0x%02X, Received: 0x%02X", calculate_crc8(&data[9]), pm10_crc);
        //return ESP_ERR_INVALID_CRC;
    }
    else{
		//ESP_LOGI(TAG, "PM10 CRC Correct!");

	}
    //pm10 = pm10_raw / 10.0; // Scale factor is 10
    //pm10 = 2.3350992860750863*pm10 + (1.1038457405169595);

    // Log the parsed values
    //ESP_LOGI(TAG, "PM2.5: %.1f ", pm25);
    //ESP_LOGI(TAG, "PM10: %.1f  ", pm10);

 //return pm25, pm10;
}
esp_err_t stop_measurement() {
    // For example, send a hypothetical stop command (replace with actual command if available)
    uint8_t cmd[] = {0x01, 0x04}; // This is only an example command!
    esp_err_t ret = i2c_master_write_to_device(I2C_NUM, SEN55_I2C_ADDRESS, cmd, sizeof(cmd), pdMS_TO_TICKS(1000));
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SEN 55] Failed to stop measurement: %s", esp_err_to_name(ret));
    } else {
        ESP_LOGI(TAG, "[SEN 55] Measurement stopped (sensor is idle).");
    }
    return ret;
}

void sen55_task(void *vParameters){
	start_measurement_sen55();
	vTaskDelay(pdMS_TO_TICKS(7000));
	while (true) {
    	if (check_data_ready_flag() == 1) {
        	if (xSemaphoreTake(i2c_mutex, portMAX_DELAY)) {
            	read_measured_values_sen55();
            	xSemaphoreGive(i2c_mutex);
        	}        	//printf("PM2.5: %.1f, PM10: %.1f", pm25, pm10);
        }
        vTaskDelay(pdMS_TO_TICKS(1000));
        //stop_measurement();
        vTaskDelay(pdMS_TO_TICKS(29000)); // Poll every 5 seconds
        //start_measurement_sen55();
        vTaskDelay(pdMS_TO_TICKS(30000));
    }
}
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


esp_err_t scd41_start_periodic_measurement(void) {
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_START_PERIODIC_MEASUREMENT_CMD >> 8),
        (uint8_t)(SCD41_START_PERIODIC_MEASUREMENT_CMD & 0xFF)
    };

    // Send the command to start periodic measurement
    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_SCD41_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "[SCD41] Started periodic measurement");
    } else {
        ESP_LOGE(TAG, "[SCD41] Failed to start periodic measurement: %s", esp_err_to_name(ret));
    }

    return ret;
}

void scd41_read_measurement() {
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_READ_MEASUREMENT_CMD >> 8),
        (uint8_t)(SCD41_READ_MEASUREMENT_CMD & 0xFF)
    };

    uint8_t data[8] = {0}; // Buffer to hold raw sensor data

    // Send the command to read measurement data
    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_SCD41_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "Error! %s", esp_err_to_name(ret));
        //return ret;
    }

    // Read the response from the sensor
    cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_READ, true);
    i2c_master_read(cmd_handle, data, sizeof(data), I2C_MASTER_LAST_NACK);
    i2c_master_stop(cmd_handle);

    ret = i2c_master_cmd_begin(I2C_SCD41_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret == ESP_OK) {
        uint16_t co2_raw = (data[0] << 8) | data[1]; // Raw CO2 value
        uint16_t temperature_raw = (data[3] << 8) | data[4]; // Raw temperature value
        uint16_t humidity_raw = (data[6] << 8) | data[7]; // Raw humidity value

        // Convert raw values to meaningful units
        co2 = co2_raw; // CO2 is directly in ppm
        float temperature_celsius = -45.0 + (175.0 * ((float)temperature_raw / 65536.0)); //From datasheet
        float humidity_percent = 100.0 * ((float)humidity_raw / 65536.0); //From datasheet

		//ESP_LOGI(TAG, "CO2: %.0f ppm, Temperature: %.2fC, Humidity: %.2f%%", co2, temperature_celsius, humidity_percent);
    } 
    else {
        ESP_LOGE(TAG, "[SCD41] Failed to read! %s", esp_err_to_name(ret));
    }

    //return ret;
}

esp_err_t scd41_reinit(void) {
    uint8_t cmd[2] = { 0x36, 0x46 }; // Re-initialization command

    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_SCD41_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);
    return ret;
}

esp_err_t scd41_stop_periodic_measurement(void) {
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_STOP_PERIODIC_MEASUREMENT_CMD >> 8),
        (uint8_t)(SCD41_STOP_PERIODIC_MEASUREMENT_CMD & 0xFF)
    };

    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_SCD41_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "[SCD41] Stopped periodic measurement");
    } else {
        ESP_LOGE(TAG, "[SCD41] Failed to stop periodic measurement: %s", esp_err_to_name(ret));
    }

    return ret;
}

// Function to send command to trigger a single shot measurement
esp_err_t scd41_single_shot_measurement(void) {
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_SINGLE_SHOT_MEASUREMENT_CMD >> 8),
        (uint8_t)(SCD41_SINGLE_SHOT_MEASUREMENT_CMD & 0xFF)
    };

    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "[SCD41] Single shot measurement command sent");
    } else {
        ESP_LOGE(TAG, "[SCD41] Failed to send single shot command: %s", esp_err_to_name(ret));
    }
    return ret;
}

// Function to start low power periodic measurement mode
esp_err_t scd41_start_low_power_periodic_measurement(void) {
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_START_LOW_POWER_PERIODIC_MEASUREMENT_CMD >> 8),
        (uint8_t)(SCD41_START_LOW_POWER_PERIODIC_MEASUREMENT_CMD & 0xFF)
    };

    // Send the command to start low power periodic measurement
    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "[SCD41] Started low power periodic measurement");
    } else {
        ESP_LOGE(TAG, "[SCD41] Failed to start low power periodic measurement: %s", esp_err_to_name(ret));
    }

    return ret;
}

void scd41_task(void *vParameters){
	
	vTaskDelay(pdMS_TO_TICKS(2000));
	vTaskDelay(pdMS_TO_TICKS(1000));
	scd41_start_periodic_measurement();
	//scd41_start_low_power_periodic_measurement();
	
	while (true) {
		//scd41_single_shot_measurement();
		vTaskDelay(pdMS_TO_TICKS(6000));
    	
        if (xSemaphoreTake(i2c_mutex, portMAX_DELAY)) {
            scd41_read_measurement();
            vTaskDelay(pdMS_TO_TICKS(60000)); // Poll every 5 seconds
            xSemaphoreGive(i2c_mutex);
        }
        //vTaskDelay(pdMS_TO_TICKS(2000)); // Poll every 5 seconds
    }

}
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 📊 Read ADC & Convert to Voltage (mV)
static int read_adc_voltage(adc_channel_t channel) {
    int raw_value = 0;
    int calibrated_value = 0;

    ESP_ERROR_CHECK(adc_oneshot_read(adc1_handle, channel, &raw_value));

    if (adc1_cali_handle) {
        ESP_ERROR_CHECK(adc_cali_raw_to_voltage(adc1_cali_handle, raw_value, &calibrated_value));
    } else {
        // ⚠ Manual Scaling if Calibration Fails
        calibrated_value = ((raw_value - ADC_RAW_MIN_MICS) * ADC_VOLTAGE_MAX_MICS) / (ADC_RAW_MAX_MICS - ADC_RAW_MIN_MICS);
    }

    ESP_LOGI(TAG, "Channel %d: Raw: %d, Voltage: %.5f mV", channel, raw_value, (double)calibrated_value);

    return calibrated_value;
}

static void init_adc1(void) {
    ESP_LOGI(TAG, "Initializing ADC 1...");

    adc_oneshot_unit_init_cfg_t unit_config = {
        .unit_id = ADC_UNIT_1,
    };
    ESP_ERROR_CHECK(adc_oneshot_new_unit(&unit_config, &adc1_handle));

    adc_oneshot_chan_cfg_t channel_config = {
        .bitwidth = ADC_BITWIDTH_DEFAULT,
        .atten = ADC_ATTEN_DB_11,  // ⚡ Set for 0–2.2V input range
    };
    ESP_ERROR_CHECK(adc_oneshot_config_channel(adc1_handle, ADC1_CH1_RED, &channel_config));
    ESP_ERROR_CHECK(adc_oneshot_config_channel(adc1_handle, ADC1_CH2_NOX, &channel_config));

    // Calibration Setup
    adc_cali_curve_fitting_config_t cali_config = {
        .unit_id = ADC_UNIT_1,
        .atten = ADC_ATTEN_DB_11,
        .bitwidth = ADC_BITWIDTH_DEFAULT,
    };

    esp_err_t ret = adc_cali_create_scheme_curve_fitting(&cali_config, &adc1_cali_handle);
    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "ADC 1 calibration initialized successfully.");
    } else {
        ESP_LOGW(TAG, "ADC 1 calibration failed. Readings may be inaccurate.");
        adc1_cali_handle = NULL;
    }
}

void mics_task(void *vParameters){
	init_adc1();
	vTaskDelay(pdMS_TO_TICKS(9000));
	
	while (1) {
		
        float voltage_red = read_adc_voltage(ADC1_CH1_RED);
        float voltage_nox = read_adc_voltage(ADC1_CH2_NOX);
        
        //FOR CALIBRATION ONLY!!!!!!
		//co = voltage_red;
		//no2 = voltage_nox;
        
        voltage_red=voltage_red / 1000.0;
        voltage_nox=voltage_nox / 1000.0;
        
        double Rs_co = (5-voltage_red) / (voltage_red/47000);
		double Rs_no2 = (5-voltage_nox) / (voltage_nox/22000);
		//ESP_LOGI(TAG, "Rs -> CO: %.2f ohms, NO2: %.2f ohms",voltage_red, voltage_nox);
                 
		//For CO readings
		co = pow(10, -1.1859 * (log(Rs_co/R0_co) / M_LN10) + 0.6201); //Curve Fitting Equation from Source
		//For NO2 readings	
		no2 = pow(10, 0.9682 * (log(Rs_no2/R0_no2) / M_LN10) - 0.8108); //Curve Fitting Equation from Source
		
		

        //ESP_LOGI(TAG, "Processed Results -> CO: %.2f ppm, NO2: %.2f ppm",voltage_red / 1000.0, voltage_nox / 1000.0);

        vTaskDelay(pdMS_TO_TICKS(1000));  // Delay 1s
    }

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
static float read_so2_concentration(void) {
	float sum_gas = 0.0f, sum_ref = 0.0f;

    // 60 samples, one per second
    
    	// --- OVERSAMPLING BLOCK ---
        uint32_t raw_acc_gas = 0;
        uint32_t raw_acc_ref = 0;

        for (int j = 0; j < OVERSAMPLE_COUNT; j++) {
			int raw_vgas = 0, raw_vref = 0;
            ESP_ERROR_CHECK(adc_oneshot_read(adc1_handle, ADC_CHANNEL_VGAS, &raw_vgas));
            ESP_ERROR_CHECK(adc_oneshot_read(adc1_handle, ADC_CHANNEL_VREF, &raw_vref));

            raw_acc_gas += (uint32_t)raw_vgas;
            raw_acc_ref += (uint32_t)raw_vref;
        }

        // average raw codes
        uint32_t raw_avg_gas = raw_acc_gas / OVERSAMPLE_COUNT;
        uint32_t raw_avg_ref = raw_acc_ref / OVERSAMPLE_COUNT;

        // convert averaged codes to millivolts
        int cal_gas_mv = 0, cal_ref_mv = 0;
        if (adc1_cali_handle) {
            ESP_ERROR_CHECK(adc_cali_raw_to_voltage(adc1_cali_handle, raw_avg_gas, &cal_gas_mv));
            ESP_ERROR_CHECK(adc_cali_raw_to_voltage(adc1_cali_handle, raw_avg_ref, &cal_ref_mv));
        } else {
            ESP_LOGW(TAG, "No ADC calibration, using raw codes as mV!");
            cal_gas_mv = (int)raw_avg_gas;
            cal_ref_mv = (int)raw_avg_ref;
        }
        float gas_voltage = (float)cal_gas_mv;
        float ref_voltage = (float)cal_ref_mv;
        float diff       = gas_voltage - ref_voltage;
            
      	ESP_LOGI(TAG, "Raw Vgas=%" PRIu32 ", Raw Vref=%" PRIu32, raw_avg_gas, raw_avg_ref);
		ESP_LOGI(TAG, "Vgas=%7.2f mV, Vref=%7.2f mV, Diff=%7.2f mV", gas_voltage, ref_voltage, diff);
          	
        sum_gas += gas_voltage;
        sum_ref += ref_voltage;
	
   	
    float M = sensitivity * gain * 0.000000001 * 1000 * 1000;
	so2 = (1.0 / M) * (cal_gas_mv - (cal_ref_mv + offset));
	so2_ppm=so2;
	
	//FOR CALIBRATION ONLY!!!!!!!
	pm25 = cal_gas_mv;
	pm10 = cal_ref_mv;
	//ESP_LOGI(TAG, "Vgas: %5d, Vref: %5d ", cal_gas_mv, cal_ref_mv);

	

    return so2_ppm;
}

static void init_adc(void) {
    ESP_LOGI(TAG, "Initializing ADC 2...");

    // ADC unit configuration
    //adc_oneshot_unit_init_cfg_t unit_config = {
        //.unit_id = ADC_UNIT_1,
    //};
    //ESP_ERROR_CHECK(adc_oneshot_new_unit(&unit_config, &adc1_handle));

    // ADC channel configuration
    adc_oneshot_chan_cfg_t channel_config = {
        .bitwidth = ADC_BITWIDTH_DEFAULT,
        .atten = ADC_ATTEN_DB_11, // Configure for 0-3.6V range
    };

    ESP_ERROR_CHECK(adc_oneshot_config_channel(adc1_handle, ADC_CHANNEL_VGAS, &channel_config));
    ESP_ERROR_CHECK(adc_oneshot_config_channel(adc1_handle, ADC_CHANNEL_VREF, &channel_config));

    // ADC calibration configuration
    adc_cali_curve_fitting_config_t cali_config = {
        .unit_id = ADC_UNIT_1,
        .atten = ADC_ATTEN_DB_11,
        .bitwidth = ADC_BITWIDTH_DEFAULT,
    };

    esp_err_t ret = adc_cali_create_scheme_curve_fitting(&cali_config, &adc1_cali_handle);
    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "ADC 2 calibration initialized successfully.");
    } else {
        ESP_LOGW(TAG, "ADC 2 calibration failed. Readings may be inaccurate.");
        adc1_cali_handle = NULL;
    }
}

void ulpsm_task(void *vParameters){
	vTaskDelay(pdMS_TO_TICKS(6000)); // Delay 2 second
	init_adc();
	vTaskDelay(pdMS_TO_TICKS(3000)); // Delay 2 second
	
	while (1) {
        so2 = read_so2_concentration();
        //read_so2_concentration();
        ESP_LOGI(TAG, "SO2 Concentration: %.2f ppm", so2_ppm);
        vTaskDelay(pdMS_TO_TICKS(1000)); // Delay 2 second
    }

}

static uint8_t scd41_crc8(const uint8_t *data, uint8_t count) {
    uint8_t crc = 0xFF;
    for (uint8_t i = 0; i < count; i++) {
        crc ^= data[i];
        for (uint8_t j = 0; j < 8; j++) {
            if (crc & 0x80)
                crc = (crc << 1) ^ 0x31;
            else
                crc <<= 1;
        }
        crc &= 0xFF;
    }
    return crc;
}

// Function to set automatic self calibration (ASC) on or off
esp_err_t scd41_set_asc(bool enable) {
    // Prepare command bytes (big-endian)
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_SET_ASC_CMD >> 8),
        (uint8_t)(SCD41_SET_ASC_CMD & 0xFF)
    };
    
    // Parameter: 0x0001 for enabled, 0x0000 for disabled
    uint16_t param = enable ? 0x0001 : 0x0000;
    uint8_t param_bytes[2] = {
        (uint8_t)(param >> 8),
        (uint8_t)(param & 0xFF)
    };
    
    // Compute CRC for the parameter bytes.
    uint8_t crc = scd41_crc8(param_bytes, 2);
    
    // Construct the full command: command bytes + parameter bytes + CRC
    uint8_t data_to_send[5] = {
        cmd[0], cmd[1], param_bytes[0], param_bytes[1], crc
    };

    // Send the command via I2C
    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, data_to_send, sizeof(data_to_send), true);
    i2c_master_stop(cmd_handle);

    esp_err_t ret = i2c_master_cmd_begin(I2C_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);

    if (ret == ESP_OK) {
        ESP_LOGI(TAG, "[SCD41] Automatic self calibration %s", enable ? "enabled" : "disabled");
    } else {
        ESP_LOGE(TAG, "[SCD41] Failed to set automatic self calibration: %s", esp_err_to_name(ret));
    }
    return ret;
}

// Function to get the current ASC status
// Returns ESP_OK if the status is read correctly and sets *asc_enabled accordingly.
esp_err_t scd41_get_asc(bool *asc_enabled) {
    // Prepare the command to get ASC status (0x2313)
    uint8_t cmd[2] = {
        (uint8_t)(SCD41_GET_ASC_CMD >> 8),
        (uint8_t)(SCD41_GET_ASC_CMD & 0xFF)
    };

    // Send the command
    i2c_cmd_handle_t cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_WRITE, true);
    i2c_master_write(cmd_handle, cmd, sizeof(cmd), true);
    i2c_master_stop(cmd_handle);
    
    esp_err_t ret = i2c_master_cmd_begin(I2C_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SCD41] Failed to send get ASC command: %s", esp_err_to_name(ret));
        return ret;
    }
    
    // Wait 1 ms for command execution as per datasheet
    vTaskDelay(1 / portTICK_PERIOD_MS);
    
    // Read the response: two data bytes and one CRC byte (total 3 bytes)
    uint8_t response[3] = {0};
    cmd_handle = i2c_cmd_link_create();
    i2c_master_start(cmd_handle);
    i2c_master_write_byte(cmd_handle, (SCD41_I2C_ADDRESS << 1) | I2C_MASTER_READ, true);
    i2c_master_read(cmd_handle, response, 2, I2C_MASTER_ACK);
    i2c_master_read_byte(cmd_handle, &response[2], I2C_MASTER_NACK);
    i2c_master_stop(cmd_handle);
    
    ret = i2c_master_cmd_begin(I2C_NUM, cmd_handle, 1000 / portTICK_PERIOD_MS);
    i2c_cmd_link_delete(cmd_handle);
    
    if (ret != ESP_OK) {
        ESP_LOGE(TAG, "[SCD41] Failed to read ASC status: %s", esp_err_to_name(ret));
        return ret;
    }
    
    // Verify CRC for the received data bytes
    uint8_t calc_crc = scd41_crc8(response, 2);
    if (calc_crc != response[2]) {
        ESP_LOGE(TAG, "[SCD41] CRC mismatch for ASC status: calculated 0x%02X, received 0x%02X", calc_crc, response[2]);
        return ESP_FAIL;
    }
    
    // Combine the two data bytes to form the status word
    uint16_t status = (response[0] << 8) | response[1];
    *asc_enabled = (status == 0x0001) ? true : false;
    
    ESP_LOGI(TAG, "[SCD41] Automatic self calibration is %s", *asc_enabled ? "enabled" : "disabled");
    return ESP_OK;
}

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

void display_task(void *vParameters){
	
	
	while(1){
		while (1) {
			data_ready=1;
			if(data_ready==0){
				snprintf(payloadd, sizeof(payloadd), "No Payload / Initializing");
			}
			else{
				// --- Read current time from DS3231 and update global Unix time string ---
		        struct tm rtc_time;
		        memset(&rtc_time, 0, sizeof(rtc_time));
		        if (ds3231_get_time(&rtc_time) == ESP_OK) {
		            // Convert the struct tm to Unix time
		            time_t current_unix = mktime(&rtc_time);
		            // Update the global string variable (in Unix seconds as string)
		            snprintf(g_synced_time_str, sizeof(g_synced_time_str), "%ld", (long)current_unix);
		            //ESP_LOGI(TAG, "Current DS3231 Unix Time: %s", g_synced_time_str);
		        } else {
		            ESP_LOGE(TAG, "Failed to read DS3231 time");
		        }
				//printf("\nCO2: %.1f, PM2.5: %.1f, PM10: %.1f, CO: %.1f, NO2: %.1f, SO2: %.1f \n", co2, pm25, pm10, co, no2, so2);
				//snprintf(payloadd, sizeof(payloadd), "--FROM AQ1-- CO2: %.1f, PM2.5: %.1f, PM10: %.1f, CO: %.1f, NO2: %.1f, SO2: %.1f, MAC: %s, Time: %lld\n", co2, pm25, pm10, co, no2, so2, global_mac_str,(long long)now);
				snprintf(payloadd, sizeof(payloadd), "{\"type\": \"data\", \"source\": \"%s\", \"local_time\": \"%s\", \"lat\": \"%.6f\", \"long\": \"%.6f\", \"SEN55_PM25\":\"%.5f\", \"SEN55_PM10\":\"%.5f\", \"SCD41_CO2\":\"%.1f\", \"MICS4514_CO\":\"%.5f\", \"MICS4514_NO2\":\"%.5f\", \"ULPSM_SO2\":\"%.1f\"}", TAG, g_synced_time_str, lat, longi, pm25, pm10, co2, co, no2, so2);

	        }
	        vTaskDelay(pdMS_TO_TICKS(5000)); // Poll every 60 seconds
	    }
	}

}

void app_main(void)
{
	esp_log_level_set("*", ESP_LOG_NONE);  // Disable all logs
    esp_log_level_set(TAG, ESP_LOG_INFO);  // Enable only your application's logs
	
	i2c_mutex = xSemaphoreCreateMutex();
	configure_led();
	update_global_mac_string();
	
	esp_vfs_eventfd_config_t eventfd_config = {
        .max_fds = 3,
    };

    ESP_ERROR_CHECK(nvs_flash_init());
    ESP_ERROR_CHECK(esp_event_loop_create_default());
    ESP_ERROR_CHECK(esp_netif_init());
    ESP_ERROR_CHECK(esp_vfs_eventfd_register(&eventfd_config));
    
	vTaskDelay(pdMS_TO_TICKS(2000));
	ESP_LOGI(TAG, "Initializing Thread network");
	xTaskCreate(ot_task_worker, "ot_task_worker", 10240, NULL, 5, NULL);
	
	while (connected == 0) {
		ESP_LOGI(TAG, "Waiting for Thread network connection...");
		vTaskDelay(pdMS_TO_TICKS(1000)); // Wait 1 second before checking again
	}
	
		
	ESP_LOGI(TAG, "Connected to the Thread Network Successfully!");
	vTaskDelay(pdMS_TO_TICKS(2000));
	
	/*while (time_established == 0) {
		ESP_LOGI(TAG, "Syncing Time");
		vTaskDelay(pdMS_TO_TICKS(1000)); // Wait 1 second before checking again
	}*/
	
	ESP_LOGI(TAG, "Initializing I2C Communications");
	ESP_ERROR_CHECK(ds3231_i2c_master_init());
	vTaskDelay(pdMS_TO_TICKS(2000));
	
	i2c_master_init(I2C_NUM, I2C_SDA, I2C_SCL, I2C_FREQ_HZ); // one bus for I2C
	vTaskDelay(pdMS_TO_TICKS(2000));
	
	/*while (time_established == 0) {
		ESP_LOGI(TAG, "Syncing Time");
		vTaskDelay(pdMS_TO_TICKS(1000)); // Wait 1 second before checking again
	}*/
	
	
	scd41_stop_periodic_measurement();
	vTaskDelay(pdMS_TO_TICKS(1000));
	// Set ASC to the desired state (change 'true' to enable or 'false' to disable)
	scd41_set_asc(false);
    vTaskDelay(pdMS_TO_TICKS(1000));
    // Read and log the current ASC status
    bool asc_enabled = true;
    if (scd41_get_asc(&asc_enabled) != ESP_OK) {
        ESP_LOGE(TAG, "Error reading ASC status.");
    }
	
	//ESP_LOGI(TAG, "[3 min left] Heating time for the sensors!");
	//vTaskDelay(pdMS_TO_TICKS(168000)); // UNCOMMENT TO ENABLE PRE-HEATING TIME OF 3 MINUTES (MiCS-4514) 
	
	vTaskDelay(pdMS_TO_TICKS(2000));
	
	//xTaskCreate(sen55_task, "SEN55_Task", 4096, NULL, 4, NULL);
	//xTaskCreate(scd41_task, "SCD41_Task", 4096, NULL, 3, NULL);
	xTaskCreate(mics_task, "MICS_Task", 4096, NULL, 2, NULL);
	xTaskCreate(ulpsm_task, "ULPSM_Task", 4096, NULL, 1, NULL);
	
	vTaskDelay(pdMS_TO_TICKS(23000));
	xTaskCreate(display_task, "Display_Task", 4096, NULL, 1, NULL);
		


}
