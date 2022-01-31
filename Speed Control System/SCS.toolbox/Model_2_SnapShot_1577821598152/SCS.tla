-------------------------------------------- MODULE SCS ----------------------------------------------
EXTENDS Integers

VARIABLES leverState, ccState, speed, desiredSpeed\*, speedStates

End == speed /= 1 

TypeOK == /\ speed \in 1..4
          /\ desiredSpeed \in 1..4
          
\*speedStates == <<"stopped", "slow", "medium", "fast">>

Init == /\ leverState = "off"
        /\ ccState    = "off"
        /\ speed = 2
        /\ desiredSpeed = 3
       
TurnLeverOn == /\ leverState'   = "on"
               /\ ccState'      = "on"
               /\ speed'        = desiredSpeed
               /\ desiredSpeed' = desiredSpeed 
        
TurnLeverOff == /\ leverState    = "on"
                /\ ccState       = "on"
                /\ leverState'   = "off"
                /\ ccState'      = "off"
                /\ speed'        = speed
                /\ desiredSpeed' = desiredSpeed
                
IncreaseSpeed == /\ speed         /= 4
                 /\ leverState'   = leverState
                 /\ ccState'      = ccState
                 /\ speed'        = speed + 1
                 /\ desiredSpeed' = desiredSpeed
                 
DecreaseSpeed == /\ speed         /= 1
                 /\ leverState'   = leverState
                 /\ ccState'      = ccState
                 /\ speed'        = speed - 1
                 /\ desiredSpeed' = desiredSpeed 
                        
Next == \/ TurnLeverOn 
        \/ TurnLeverOff
        \/ IncreaseSpeed
        \*\/ DecreaseSpeed




===========================================================================================================
\* Modification History
\* Last modified Tue Dec 31 19:46:14 WET 2019 by ricardo