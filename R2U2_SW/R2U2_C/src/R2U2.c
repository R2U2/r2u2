#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <limits.h>
/* From vendored libs */
#include "csvparser.h"
#include "decodeCSV.h"

#include "R2U2Config.h"
#include "binParser/parse.h"
#include "TL/TL_observers.h"
#include "AT/at_checkers.h"


// #define ONLINE_MODE  //test in online mode (realtime change the input file)

void sys_init(char *argv[]) {
    /* Engine Initialization */
    TL_init();
    at_checkers_init();
    //TL_init_files("src/inputs/tmp.ftm","src/inputs/tmp.fti","src/inputs/tmp.ftscq");
    TL_init_files(argv[2],argv[3],argv[4]);
}



int main(int argc, char *argv[]) {
    //
    if (argc != 2) {
        fprintf(stdout,"%s Version %d.%d\n",
                argv[0],
                R2U2_C_VERSION_MAJOR,
                R2U2_C_VERSION_MINOR);
        fprintf(stdout, "Usage: 1) trace data file, 2) .ftm, 3) .fti, 4) .ftscq\n");
    }
    r2u2_in_type *cur_sigs;
    int MAX_TIME = 0, NUM_SIG = 0;
       
    // Code for exectuing R2U2 in real-time
    #ifdef ONLINE_MODE
        MAX_TIME = INT_MAX; //max
        int preTime = -1;
        int command = 0; //-1: restart -2: terminate
        printf("waiting for the sensor data file...\n");
        while(access( argv[1], F_OK ) == -1) sleep(1); // file not exists
        count_signals(argv[1], &NUM_SIG, &MAX_TIME);
        r2u2_in_type** in_dat = (r2u2_in_type**)malloc(MAX_TIME * sizeof(r2u2_in_type*)); 
        printf("find sensor data file: %s, wait for starting command...\n",argv[1]);
        do{
            //decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
            load_signals(argv[1], NUM_SIG, MAX_TIME, in_dat);
            command = in_dat[0][0];
            sleep(1);
        }while(command!=-1 && command!=-2);

        while(command==-1) {
            printf("Starting a new session\n");
            sys_init(argv);
            printf("waiting for the first sensor data to start the RV...\n");
            do{

                //decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
                load_signals(argv[1], NUM_SIG, MAX_TIME, in_dat);
                command = in_dat[0][0];
                sleep(0.5);
            }while(command!=0);
            
            /* Open File Output  */
            FILE *out_file, *log_file;
            out_file = fopen("./R2U2.out", "w+");
            log_file = fopen("./R2U2.log", "w+");
            if ((out_file == NULL) || (log_file == NULL)) return 1;
            /*Async file I/O */
            
            // fprintf(log_file, "**********RESULTS**********\n\n"); 
            /* Main processing loop */
            for (int cur_time=0; ; cur_time++) {
                while(true) {
                    //decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
                    load_signals(argv[1], NUM_SIG, MAX_TIME, in_dat);
                    int curTime= in_dat[0][0];
                    command = in_dat[0][0];
                    if(command<0) break;
                    if(preTime!=curTime) { // new data come in
                        if(preTime+1!=curTime) printf("Warning: Missing a time stamp.\n");
                        preTime = curTime;
                        break;
                    }
                    preTime = curTime;
                    sleep(1); // check the command every 1 s
                }
                if(command<0) break;
                //for (int i=1; i<NUM_SIG; i++) cur_sigs[i] = in_dat[0][i]; //first number is the command
                cur_sigs = &in_dat[cur_time][0]; 
                printf("\n**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****\n",cur_time);
                fprintf(out_file, "**********CURRENT TIME STEP: %d**********\n\n", cur_time);
                fprintf(log_file, "----------TIME STEP: %d----------\n", cur_time);
                /* Atomics Update */
                at_checkers_update(cur_sigs); //update atomic_vector
                /* Temporal Logic Update */
                TL_update(out_file, log_file);

                fprintf(out_file,"\n\n");
                fprintf(log_file, "\n");
            }
            fclose(out_file);
            fclose(log_file);
        }
    }
    // Code for executing R2U2 in simulated time
    #else
        sys_init(argv);
        count_signals(argv[1], &NUM_SIG, &MAX_TIME);
        //decodeCSV(argv[1],&in_dat,&MAX_TIME,&NUM_SIG);
        r2u2_in_type** in_dat = (r2u2_in_type**)malloc(MAX_TIME * sizeof(r2u2_in_type*)); 
        load_signals(argv[1], NUM_SIG, MAX_TIME, in_dat);
        FILE *out_file, *log_file;
        out_file = fopen("./R2U2.out", "w+");
        log_file = fopen("./R2U2.log", "w+");
        
        
        if((out_file == NULL) || (log_file == NULL)) return 1;

        // R2U2 Output headers
        printf("**********RESULTS**********\n");
        fprintf(log_file, "**********RESULTS**********\n");
        
        /* Main processing loop */
        int cur_time = 0;
        for(cur_time = 0; cur_time < MAX_TIME; cur_time++) {
            cur_sigs = &in_dat[cur_time][0]; 
            
            // Terminal and log file headings, when in debug mode
            #ifdef DEBUG
                // Print to the terminal
                printf("\n**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****\n",cur_time);
                // Print to the '.out' file
                fprintf(out_file, "**********CURRENT TIME STEP: %d**********\n\n", cur_time);
                // Print to the '.log' file
                fprintf(log_file, "----------TIME STEP: %d----------\n", cur_time);               
            #endif
            
            /* Atomics Update */
            at_checkers_update(cur_sigs); //update atomic_vector
            /* Temporal Logic Update */
            TL_update(out_file, log_file);

        }
        fclose(out_file);
        fclose(log_file);
    #endif
  
    return 0;
}

