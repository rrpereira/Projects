-------------------------------------------- MODULE SCS ----------------------------------------------
EXTENDS Integers

VARIABLES lever, cc, speed, desiredSpeed\*, speedStates

TypeOK == /\ speed \in 1..4
          /\ desiredSpeed \in 1..4
          /\ lever \in {"on", "off"}
          /\ cc \in {"on", "off"}         
\*speedStates == <<"stopped", "slow", "medium", "fast">>

Init == /\ lever        = "off"
        /\ cc           = "off"
        /\ speed        = 2
        /\ desiredSpeed = 3
    
\* Apenas coloca a speed com o valor da desiredSpeed mas pretende-se que seja algo gradual
EqualsDesiredSpeed == IF speed < desiredSpeed
                        THEN speed' = desiredSpeed
                        ELSE IF speed = desiredSpeed
                            THEN speed' = desiredSpeed
                            ELSE speed' = desiredSpeed
                       
Break == /\ lever'        = "off" 
         /\ cc            = "off"
         /\ lever'        = "off"
         /\ speed'        = speed
         /\ desiredSpeed' = desiredSpeed
                        
TurnLeverOn == /\ lever'        = "on"
               /\ cc'           = "on"
               /\ EqualsDesiredSpeed 
               /\ desiredSpeed' = desiredSpeed 
        
TurnLeverOff == /\ lever         = "on"
                /\ cc            = "on"
                /\ lever'        = "off"
                /\ cc'           = "off"
                /\ speed'        = speed
                /\ desiredSpeed' = desiredSpeed
                
IncreaseSpeed == /\ speed         /= 4
                 /\ lever'        = lever
                 /\ cc'           = cc
                 /\ speed'        = speed + 1
                 /\ desiredSpeed' = desiredSpeed
                 
DecreaseSpeed == /\ speed         /= 1
                 /\ lever'        = lever
                 /\ cc'           = cc
                 /\ speed'        = speed - 1
                 /\ desiredSpeed' = desiredSpeed 
                        
Next == \/ TurnLeverOn 
        \/ TurnLeverOff
        \/ IncreaseSpeed
        \/ DecreaseSpeed
        \/ Break




===========================================================================================================
\* Modification History
\* Last modified Tue Dec 31 20:29:43 WET 2019 by ricardo