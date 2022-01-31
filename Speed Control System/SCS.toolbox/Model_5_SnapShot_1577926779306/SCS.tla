-------------------------------------------- MODULE SCS ----------------------------------------------
(*********************************************************************************)
(* This specification expresses the actions/states that happens arround cruise   *)
(* control system. Speed increase/decrease, car braking, etc are some behaviours *)
(* that are somehow realated with a car with cruise control system.              *)
(*********************************************************************************)
EXTENDS Integers


                          (*##########################*)                             


VARIABLES cc, desiredLimit, desiredSpeed, lever, sl, speed
(*********************************************************************************)


                          (*##########################*)


\* Macro variables are established below.
stopped  == 1
minSpeed == 2
maxSpeed == 6


                          (*##########################*)


(*********************************************************************************)
(* Anyone who wants to see if something is working/happening must enter below    *)
(* a predicate (which will be an invariant) where model will certainly fail, in  *) 
(* order to see the steps until the desired state.                               *) 
(*********************************************************************************)
End == ~(speed = desiredLimit /\ sl = "on")


                          (*##########################*)


(*********************************************************************************)
(* This predicate is an invariant and remains true across all of the states.     *)
(*********************************************************************************)
TypeOK == /\ cc \in {"on", "off"}
          /\ desiredLimit \in minSpeed..maxSpeed \* 2-slow 3-medium 4-fast
          /\ desiredSpeed \in minSpeed..maxSpeed \*2-slow 3-medium 4-fast
          /\ lever \in 0..5
          /\ sl \in {"on", "off"}
          /\ speed \in stopped..maxSpeed \* 1-stopped 2-slow 3-medium 4-fast


                          (*##########################*)


\* The speed limit is either - on and respected - or - off.
SpeedUnderDesiredLimit == \/ (speed <= desiredLimit /\ sl = "on")
                          \/ (sl = "off")

(*********************************************************************************)
(* This predicate is another invariant and remains true across all of the        *)
(* states. It's different than the other above because it assures properties not *)
(* related with variables types.                                                 *)
(*********************************************************************************)

PropertiesOK == /\ SpeedUnderDesiredLimit 
           
           
                          (*##########################*)                   
           
                                                         
\* Defines initial state.
Init == /\ cc           = "off"
        /\ desiredLimit = 4
        /\ desiredSpeed = 2
        /\ lever        = 0
        /\ sl           = "off"
        /\ speed        = 3
    
    
                          (*##########################*)    
    
      
\* Puts speed with desiredSpeed value instantly (but we want to make it gradual)
ApproachesDesiredSpeed == IF speed < desiredSpeed
                            THEN speed' = speed + 1
                            ELSE speed' = speed - 1

(*********************************************************************************)
(* Predicate that is continuously called since when the lever is turned to 1     *)
(* untill speed equals desired speed.                                            *)  
(*********************************************************************************)
EqualsDesiredSpeed == /\ cc            = "on"
                      /\ lever         = 0
                      /\ speed         /= desiredSpeed
                      /\ cc'           = cc 
                      /\ desiredLimit' = desiredLimit
                      /\ desiredSpeed' = desiredSpeed
                      /\ lever'        = lever
                      /\ sl'           = sl
                      /\ ApproachesDesiredSpeed
                                                 
\* The car brakes and reduces current speed (in one unit).             
Brake == /\ lever         = 0
         /\ speed         > stopped
         /\ cc'           = "off"
         /\ desiredLimit' = desiredLimit
         /\ desiredSpeed' = desiredSpeed
         /\ lever'        = lever   
         /\ sl'           = sl
         /\ speed'        = speed - 1   
         
\* Lever goes to it's neutral state after being manipulated.
TurnLever0 == /\ lever         /= 0 
              /\ cc'           = cc
              /\ desiredLimit' = desiredLimit
              /\ desiredSpeed' = desiredSpeed 
              /\ lever'        = 0   
              /\ sl'           = sl
              /\ speed'        = speed
          
\* Activates cruise control.  
TurnLever1 == /\ lever         = 0
              /\ cc'           = "on"
              /\ desiredLimit' = desiredLimit 
              /\ desiredSpeed' = desiredSpeed
              /\ lever'        = 1   
              /\ sl'           = sl
              /\ speed'        = speed
              \*/\ ApproachesDesiredSpeed
              
\* Increases desired speed.
TurnLever2 == \/ /\ desiredSpeed  < maxSpeed
                 /\ lever         = 0
                 /\ sl            = "off" 
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit 
                 /\ desiredSpeed' = desiredSpeed + 1
                 /\ lever'        = 2   
                 /\ sl'           = sl
                 /\ speed'        = speed
              \/ /\ desiredLimit  < maxSpeed 
                 /\ lever         = 0
                 /\ sl            = "on" 
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit + 1 
                 /\ desiredSpeed' = desiredSpeed
                 /\ lever'        = 2   
                 /\ sl'           = sl
                 /\ speed'        = speed

\* Decreases desired speed.
TurnLever3 == \/ /\ desiredSpeed  > minSpeed
                 /\ lever         = 0
                 /\ sl            = "off"
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit 
                 /\ desiredSpeed' = desiredSpeed - 1
                 /\ lever'        = 3   
                 /\ sl'           = sl
                 /\ speed'        = speed
              \/ /\ desiredLimit  > minSpeed
                 /\ lever         = 0
                 /\ sl            = "on" 
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit - 1 
                 /\ desiredSpeed' = desiredSpeed
                 /\ lever'        = 3   
                 /\ sl'           = sl
                 /\ speed'        = speed
                               
\* Deactivates cruise control.
TurnLever4 == /\ cc            = "on"
              /\ lever         = 0
              /\ cc'           = "off"
              /\ desiredLimit' = desiredLimit
              /\ desiredSpeed' = desiredSpeed
              /\ lever'        = 4   
              /\ sl'           = sl
              /\ speed'        = speed

\* Activates speed limit.
TurnLever5 == /\ cc            = "off"
              /\ lever         = 0
              /\ speed         <= desiredLimit
              /\ cc'           = cc
              /\ desiredLimit' = desiredLimit
              /\ desiredSpeed' = desiredSpeed
              /\ lever'        = 5
              /\ sl'           = "on"
              /\ speed'        = speed

(*********************************************************************************)
(* Increases current speed (in one unit) until the maximum speed is achieved or  *)
(* until speed limit is reached as long as speed limit function is activated.    *)
(*********************************************************************************)
IncreaseSpeed == \/ /\ cc            = "off"
                    /\ lever         = 0
                    /\ speed         < maxSpeed
                    /\ sl            = "off"
                    /\ cc'           = cc
                    /\ desiredSpeed' = desiredSpeed
                    /\ lever'        = lever
                    /\ speed'        = speed + 1
                    /\ desiredLimit' = desiredLimit   
                    /\ sl'           = sl  
                 \/ /\ cc            = "off"
                    /\ lever         = 0
                    /\ speed         < desiredLimit
                    /\ sl            = "on"
                    /\ cc'           = cc
                    /\ desiredLimit' = desiredLimit
                    /\ desiredSpeed' = desiredSpeed
                    /\ lever'        = lever   
                    /\ sl'           = sl
                    /\ speed'        = speed + 1
                                    
\* Decreases current speed (in one unit).                 
DecreaseSpeed == /\ cc            = "off"
                 /\ lever         = 0
                 /\ speed         > stopped
                 /\ cc'           = cc
                 /\ desiredLimit' = desiredLimit
                 /\ desiredSpeed' = desiredSpeed
                 /\ lever'        = lever   
                 /\ sl'           = sl
                 /\ speed'        = speed - 1 

\* Nothing changes.                        
NothingChanges == /\ lever         = 0
                  /\ cc'           = cc
                  /\ desiredLimit' = desiredLimit
                  /\ desiredSpeed' = desiredSpeed
                  /\ lever'        = lever   
                  /\ sl'           = sl
                  /\ speed'        = speed


                          (*##########################*)


\* Defines the next state.                        
Next == \*\/ Brake
        \*\/ DecreaseSpeed
        \/ EqualsDesiredSpeed
        \/ IncreaseSpeed
        \/ NothingChanges
        \/ TurnLever0
        \/ TurnLever1
        \*\/ TurnLever2
        \*\/ TurnLever3 
        \*\/ TurnLever4
        \/ TurnLever5


                          (*##########################*)


\* cc can be turned on when current speed is 1 (stopped)

\* acho que seria decente colocar a speed a tender para a desiredSpeed (enquanto
\*   não ficassem igualadas, fazia-se o predicado EqualsDesiredSpeed) nao tenho 
\*   a certeza se isto já está a acontecer visto que ativando o cruise control 
\*   apenas deveria ser possivel os proximos passos serem TurnLever0 (alavanca ir
\*   para o estado neutro) e EqualsDiseredSpeed até speed = desiredSpeed; enquanto
\*   desiredspeed /= speed, turnlever1,2,3,4, nothingchanges, break, etc, e esses
\*   passos todos nao deveriam acontecer -> até agora nao detetei nada que estivesse mal

\* 

===========================================================================================================
\* Modification History
\* Last modified Thu Jan 02 00:59:32 WET 2020 by ricardo