-------------------------------------------- MODULE SCS ----------------------------------------------

VARIABLES lever, cc, speed

End == speed /= "stopped" 

Init == /\ lever = "off"
        /\ cc = "off"
        /\ speed = "slow"
       
TurnLeverOn == /\ lever' = "on"
               /\ cc'    = "on"
               /\ speed' = "ccspeed"        
        
TurnLeverOff == /\ lever' = "off"
                /\ cc'    = "off"
                /\ (speed' = "slow" \/ speed' = "stopped") 
                        
Next == TurnLeverOn \/ TurnLeverOff




===========================================================================================================
\* Modification History
\* Last modified Tue Dec 31 16:54:14 WET 2019 by ricardo