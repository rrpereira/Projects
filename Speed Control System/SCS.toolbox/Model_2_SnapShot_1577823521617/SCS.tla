-------------------------------------------- MODULE SCS ----------------------------------------------
EXTENDS Integers

VARIABLES lever, ccState, speed, desiredSpeed\*, speedStates

End == speed /= 1 

TypeOK == /\ speed \in 1..4
          /\ desiredSpeed \in 1..4
          
\*speedStates == <<"stopped", "slow", "medium", "fast">>

Init == /\ lever        = "off"
        /\ ccState      = "off"
        /\ speed        = 2
        /\ desiredSpeed = 3
    
EqualsDesiredSpeed == IF speed < desiredSpeed
                        THEN speed' = desiredSpeed
                        ELSE IF speed = desiredSpeed
                            THEN speed' = desiredSpeed
                            ELSE speed' = desiredSpeed
                        
TurnLeverOn == /\ lever'        = "on"
               /\ ccState'      = "on"
               /\ EqualsDesiredSpeed 
               /\ desiredSpeed' = desiredSpeed 
        
TurnLeverOff == /\ lever         = "on"
                /\ ccState       = "on"
                /\ lever'        = "off"
                /\ ccState'      = "off"
                /\ speed'        = speed
                /\ desiredSpeed' = desiredSpeed
                
IncreaseSpeed == /\ speed       /= 4
                 /\ lever'        = lever
                 /\ ccState'      = ccState
                 /\ speed'        = speed + 1
                 /\ desiredSpeed' = desiredSpeed
                 
DecreaseSpeed == \*/\ speed       /= 1
                 /\ lever'        = lever
                 /\ ccState'      = ccState
                 /\ speed'        = speed - 1
                 /\ desiredSpeed' = desiredSpeed 
                        
Next == \/ TurnLeverOn 
        \/ TurnLeverOff
        \/ IncreaseSpeed
        \*\/ DecreaseSpeed




===========================================================================================================
\* Modification History
\* Last modified Tue Dec 31 20:18:34 WET 2019 by ricardo