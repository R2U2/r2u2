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


#define ONLINE_MODE  //test in real time

void sys_init() {
    /* Engine Initialization */
    TL_init();
    at_checkers_init();
    TL_init_files("src/inputs/tmp.ftm","src/inputs/tmp.fti","src/inputs/tmp.ftscq");
}



int main(int argc, char const *argv[]) {

    if (argc != 2) {
        fprintf(stdout,"%s Version %d.%d\n",
                argv[0],
                R2U2_C_VERSION_MAJOR,
                R2U2_C_VERSION_MINOR);
        fprintf(stdout, "Usage: input data file name\n");
    }
    r2u2_in_type **in_dat;
    r2u2_in_type *cur_sigs;
    int MAX_TIME = 0, NUM_SIG = 0;


    #ifdef ONLINE_MODE
        MAX_TIME = INT_MAX; //max
        int preTime = -1;
        int command = 0; //-1: restart -2: terminate
        printf("waiting for the sensor data file...\n");
        while(access( argv[1], F_OK ) == -1) sleep(1); // file not exists
        printf("find sensor data file: %s, wait for starting command...\n",argv[1]);
        do{
            decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
            command = in_dat[0][0];
            sleep(1);
        }while(command!=-1 && command!=-2);

        while(command==-1) {
            printf("Starting a new session\n");
            sys_init();
            printf("waiting for the first sensor data to start the RV...\n");
            do{
                decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
                command = in_dat[0][0];
                sleep(1);
            }while(command!=0);
            
            /* Open File Output  */
            FILE *out_file, *dbg_file;
            out_file = fopen("./R2U2.out", "w+");
            dbg_file = fopen("./R2U2.log", "w+");
            if ((out_file == NULL) || (dbg_file == NULL)) return 1;
            /*Async file I/O */
            
            fprintf(dbg_file, "**********RESULTS**********\n\n"); 
            /* Main processing loop */
            for (int cur_time=0; ; cur_time++) {
                while(true) {
                    decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
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
                for (int i=1; i<NUM_SIG; i++) cur_sigs[i] = in_dat[0][i]; //first number is the command
                printf("\n**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****\n",cur_time);
                fprintf(out_file, "**********CURRENT TIME STEP: %d**********\n\n", cur_time);
                fprintf(dbg_file, "----------TIME STEP: %d----------\n", cur_time);
                /* Atomics Update */
                at_checkers_update(cur_sigs); //update atomic_vector
                /* Temporal Logic Update */
                TL_update(out_file, dbg_file);

                fprintf(out_file,"\n\n");
                fprintf(dbg_file, "\n");
            }
            fclose(out_file);
            fclose(dbg_file);
        }

    #else
        decodeCSV(argv[1],&in_dat,&cur_sigs,&MAX_TIME,&NUM_SIG);
        FILE *out_file, *dbg_file;
        out_file = fopen("./R2U2.out", "w+");
        dbg_file = fopen("./R2U2.log", "w+");
        if ((out_file == NULL) || (dbg_file == NULL)) return 1;
        fprintf(dbg_file, "**********RESULTS**********\n\n"); 
        /* Main processing loop */
        for (int cur_time=0; cur_time < MAX_TIME; cur_time++) {
            for (int i=0; i<NUM_SIG; i++) cur_sigs[i] = in_dat[cur_time][i]; 
            printf("\n**** [DBG]::R2U2:: CURRENT TIME STEP: %d ****\n",cur_time);
            fprintf(out_file, "**********CURRENT TIME STEP: %d**********\n\n", cur_time);
            fprintf(dbg_file, "----------TIME STEP: %d----------\n", cur_time);
            /* Atomics Update */
            at_checkers_update(cur_sigs); //update atomic_vector
            /* Temporal Logic Update */
            TL_update(out_file, dbg_file);

            fprintf(out_file,"\n\n");
            fprintf(dbg_file, "\n");
        }
        fclose(out_file);
        fclose(dbg_file);
    #endif
  
    return 0;
}

