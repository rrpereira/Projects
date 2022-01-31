-------------------------------------------- MODULE SCS ----------------------------------------------
(*********************************************************************************)
(* This specification expresses the actions/states that happens arround cruise   *)
(* control system. Speed increase/decrease, car braking, etc are some behaviours *)
(* that are somehow realated with a car with cruise control system.              *)
(*********************************************************************************)
                          
                          
                          (*##########################*)

EXTENDS Integers


                          (*##########################*)                             


VARIABLES acousticWarn, brakePedal, cc, desiredLimit, desiredSpeed, engine, 
          frontCarGap, gasPedal, lever, sl, slWarn, speed, visualWarn


                          (*##########################*)

(*********************************************************************************)
(* Macro variables are established below.                                        *)
(*********************************************************************************)
critical       == 4
maxSpeed       == 4
minSpeed       == 2
none           == 1
safe           == 2
speedVariation == 1
stopped        == 1 
unsafe         == 3


                          (*##########################*)


(*********************************************************************************)
(* Anyone who wants to see if something is working/happening must enter below    *)
(* a predicate (which will be an invariant) where model will certainly fail, in  *) 
(* order to see the steps until the desired state.                               *) 
(*********************************************************************************)

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before speed       *) 
(* equals desiredLimit when the speed limit function is available.               *)
(*********************************************************************************)
\*End == ~(speed = desiredLimit /\ sl = "on")

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before engine      *) 
(* turns off. Note that engine's init state needs to be modified to "on" or TLC  *)
(* will always find this invariant to be false at the init state.                *)
(*********************************************************************************)
\*End == engine /= "off"

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before engine      *) 
(* turns off with speed limit function activated. Note that engine's init state  *)
(* needs to be modified to "on" or TLC will always find this invariant to be     *)
(* false at the init state.                                                      *)
(*********************************************************************************)
\*End == ~(engine = "off" /\ sl = "off")

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states before speed       *) 
(* equals desired speed in order to check if, before that and after cruise       *)
(* control is activated, the lever turns, for example, position 3.               *)
(*********************************************************************************)
\*End == ~(cc = "on" /\ speed /= desiredSpeed /\ lever = 3)

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states where desiredLimit *)
(* is either 2, 3 or 4.                                                          *)
(*********************************************************************************)
\*End == ~(desiredLimit = 2) /\ ~(desiredLimit = 3) /\ ~(desiredLimit = 4)

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states where lever turns  *)
(* to 5, which turns the speed limit function off (it also turns it on but       *)
(* that's not what we want to check here.                                        *)
(*********************************************************************************)
\*End == ~(lever = 5 /\ sl = "off")

(*********************************************************************************)
(* This invariant will force TLC to show a sequence of states where speed limit  *) 
(* LED lights up (that happens when speed limit function is activated).          *)
(*********************************************************************************)
\*End == ~(slWarn = "on")

End == 1 = 1


                          (*##########################*)
                          
                          
(*********************************************************************************)                          
(*SCS1                                                                           *)
(*********************************************************************************)
SCS1 == (engine = "off") => (desiredSpeed = none)  

(*********************************************************************************)
(*SCS2                                                                           *)
(*********************************************************************************)
SCS2 == (lever = 1) => \/ desiredSpeed = none
                       \/ speed < desiredSpeed
                       \/ speed > desiredSpeed
                       \/ speed = desiredSpeed       
                    
(*********************************************************************************)
(* SCS3 - Assuming that below 20km/h is equal to stopped.                        *)
(*********************************************************************************)
SCS3 == (speed = stopped /\ desiredSpeed = none) => cc = "off" 

(*********************************************************************************)
(* SCSA - SCSA gathers SCSs 4, 5, 7 and 8, assuming that the lever doesn't have  *)
(* resistance levels and that pushing the lever to 2 only increases the desired  *)
(* speed, under normal conditions (with speed limit function off).               *) 
(*********************************************************************************)
\*SCSA == (lever = 2 /\ sl = "off") => (desiredSpeed = desiredSpeed + speedVariation)  

(*********************************************************************************)
(* SCSB - SCSB gathers SCSs 6, 9 and 10, assuming that the lever doesn't have    *)
(* resistance levels and that pushing the lever to 3 only decreases the desired  *)
(* speed, under normal conditions (with speed limit function off).               *) 
(*********************************************************************************)
\*SCSB == (lever = 3 /\ sl = "off") => (desiredSpeed = desiredSpeed - speedVariation)
 
(*********************************************************************************)
(* SCS11                                                                         *)
(*********************************************************************************)
SCS11 == /\ lever = 2 \/ lever = 3 
         /\ cc = "off" 
         /\ sl = "off" 
         => (desiredSpeed = speed)
         
\* isto é igual ao que está em cima certo ???
\*SCS11 == ((lever = 2 \/ lever = 3) /\ cc = "off" /\ sl = "off") => (desiredSpeed = speed)
         
(*********************************************************************************)
(* SCS12                                                                         *)
(*********************************************************************************)
SCS12 == lever = 4 => cc = "off"

(*********************************************************************************)
(* SCS13                                                                         *)
(*********************************************************************************)
SCS13 == lever = 1 => cc = "on"

(*********************************************************************************)
(* SCS14                                                                         *)
(*********************************************************************************)

(*********************************************************************************)
(* SCS15                                                                         *)
(*********************************************************************************)
SCS15 == (cc = "on" /\ gasPedal = "pressed") => speed > desiredSpeed 

(*********************************************************************************)
(* SCS16                                                                         *)
(*********************************************************************************)
SCS16 == brakePedal = "pressed" => cc = "off"

(*********************************************************************************)
(* SCS17                                                                         *)
(*********************************************************************************)
SCS17 == lever = 4 => cc = "off"

(*********************************************************************************)
(* SCS18                                                                         *)
(*********************************************************************************)

(*********************************************************************************)
(* SCS19                                                                         *)
(*********************************************************************************)

(*********************************************************************************)
(* SCS25 - Assuming that visual warning is activated if the actual distance is   *)
(* either unsafe or critical.                                                    *)
(*********************************************************************************)
SCS25 == (frontCarGap = unsafe \/ frontCarGap = critical) => visualWarn = "on"

(*********************************************************************************)
(* SCS26 - Assuming that acoustic warning is activated if the actual distance is *)
(* critical.                                                                     *)
(*********************************************************************************)
SCS26 == frontCarGap = critical => acousticWarn = "on"

(*********************************************************************************)
(* SCS29                                                                         *)
(*********************************************************************************)
SCS29 == (lever = 5 /\ sl = "on") => sl = "on" 

(*********************************************************************************)
(* SCS30                                                                         *)
(*********************************************************************************)
SCS30 == /\ sl = "on" => slWarn = "on"
         /\ sl = "off" => slWarn = "off"

(*********************************************************************************)
(* SCS31                                                                         *)
(*********************************************************************************)
SCS31 == /\ ((lever = 2) /\ (sl = "on")) => speed < desiredLimit
         /\ ((lever = 3) /\ (sl = "on")) => speed <= desiredLimit  

(*********************************************************************************)
(* SCS32                                                                         *)
(*********************************************************************************)
SCS32 == sl = "on" => speed <= desiredLimit

(*********************************************************************************)
(* SCS35                                                                         *)
(*********************************************************************************)
SCS35 == /\ lever = 4 => sl = "off"
         /\ (lever = 5 /\ sl = "off") => sl = "off"
         
(*********************************************************************************)
(* This predicate assures that the following specifications are true.            *)
(*********************************************************************************)
SCSsOK == /\ SCS1
          /\ SCS2
          /\ SCS3
          \*/\ SCSA
          \*/\ SCSB
          /\ SCS11
          /\ SCS12
          /\ SCS13
          \*/\ scs14
          /\ SCS15
          /\ SCS16
          /\ SCS17
          \*/\ SCS19
          /\ SCS25
          /\ SCS26
          /\ SCS29
          /\ SCS30
          /\ SCS31
          /\ SCS32
          \*/\ SCS33
          \*/\ SCS34
          /\ SCS35
          

                          (*##########################*)


SCSsPropertiesOK == 1=1 \* (engine' = "on") => (desiredSpeed' = none)

          
                          (*##########################*)


(*********************************************************************************)
(* This predicate is an invariant and remains true across all of the states. It  *)
(* establishes the type of each variable.                                        *)
(*********************************************************************************)
TypeOK == /\ acousticWarn \in {"off", "on"}
          /\ brakePedal   \in {"pressed", "unpressed"}
          /\ cc           \in {"off", "on"}
          /\ desiredLimit \in none..maxSpeed \*1-none 2-slow 3-medium 4-fast
          /\ desiredSpeed \in none..maxSpeed \*1-none 2-slow 3-medium 4-fast
          /\ engine       \in {"off", "on"}
          /\ frontCarGap  \in none..critical \*1-none 2-safe 3-unsafe 4-critical
          /\ gasPedal     \in {"pressed", "unpressed"}
          /\ lever        \in 0..5
          /\ sl           \in {"off", "on"}
          /\ slWarn       \in {"off", "on"}
          /\ speed        \in stopped..maxSpeed \*1-stopped 2-slow 3-medium 4-fast
          /\ visualWarn   \in {"off", "on"}


                          (*##########################*)

                          
(*********************************************************************************)
(* This predicate is another invariant and remains true across all of the        *)
(* states. It's different than the other above because it assures properties not *)
(* related with variables types.                                                 *)
(*********************************************************************************)
PropertiesOK == 1 = 1 \*Not necessary.               
           
           
                          (*##########################*)                   

           
(*********************************************************************************)
(* Defines initial state.                                                        *)
(*********************************************************************************)
Init == /\ acousticWarn = "off"
        /\ brakePedal   = "unpressed"
        /\ cc           = "off"
        /\ desiredLimit = none
        /\ desiredSpeed = none
        /\ engine       = "off"
        /\ frontCarGap  = none
        /\ gasPedal     = "unpressed"
        /\ lever        = 0
        /\ sl           = "off"
        /\ slWarn       = "off"
        /\ speed        = stopped
        /\ visualWarn   = "off"
    
    
                          (*##########################*)    
    
      
(*********************************************************************************)
(* Puts speed equal to desiredSpeed.                                             *)
(*********************************************************************************)
ApproachesDesiredSpeed == IF speed < desiredSpeed
                            THEN speed' = speed + 1
                            ELSE speed' = speed - 1
                    
(*********************************************************************************)
(* The car brakes and reduces current speed (in one unit).                       *)
(*********************************************************************************)             
Brake == /\ engine        = "on"
         /\ gasPedal      = "unpressed"
         /\ lever         = 0
         /\ speed         > stopped
         /\ brakePedal'   = "pressed"
         /\ cc'           = "off"
         /\ speed'        = speed - speedVariation   
         /\ UNCHANGED<<acousticWarn, desiredLimit, desiredSpeed, engine, 
                       frontCarGap, gasPedal, lever, sl, slWarn, visualWarn>>


(*********************************************************************************)
(* Decreases front car gap from safe to unsafe or from unsafe to critical,       *)
(* activating the corresponding warnings.                                        *)
(*********************************************************************************)
DecreaseFrontCarGap == /\ cc            = "on"
                       /\ engine        = "on"
                       /\ frontCarGap   < critical
                       /\ lever         = 0 
                       /\ IF frontCarGap = 3
                            THEN /\ acousticWarn' = "on"
                                 /\ visualWarn'   = "on" 
                            ELSE IF frontCarGap = 2
                                   THEN /\ acousticWarn' = "off"
                                        /\ visualWarn'   = "on"
                                   ELSE /\ acousticWarn' = "off"
                                        /\ visualWarn'   = "off"
                       /\ frontCarGap'  = frontCarGap + 1        
                       /\ UNCHANGED<<brakePedal, cc, desiredLimit, desiredSpeed, 
                                     engine, gasPedal, lever, sl, slWarn, speed>>               
                                    
(*********************************************************************************)
(* Decreases current speed (in one unit).                                        *)
(*********************************************************************************)                 
DecreaseSpeed == /\ brakePedal    = "unpressed"
                 /\ cc            = "off"
                 /\ engine        = "on"
                 /\ gasPedal      = "unpressed"
                 /\ lever         = 0
                 /\ speed         > stopped
                 /\ speed'        = speed - speedVariation
                 /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                               desiredSpeed, engine, frontCarGap, gasPedal, 
                               lever, sl, slWarn, visualWarn>>
                 
(*********************************************************************************)
(* Predicate that is continuously called since when the lever is turned to 1     *)
(* untill speed equals desired speed.                                            *)  
(*********************************************************************************)
EqualsDesiredSpeed == /\ brakePedal    = "unpressed"
                      /\ cc            = "on"
                      /\ desiredSpeed  /= none
                      /\ engine        = "on"
                      /\ gasPedal      = "unpressed"
                      /\ lever         = 0
                      /\ speed         /= desiredSpeed
                      /\ ApproachesDesiredSpeed 
                      /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                                    desiredSpeed, engine, frontCarGap, gasPedal, 
                                    lever, sl, slWarn, visualWarn>>
                      
(*********************************************************************************)
(* Increases front car gap from critical to unsafe or from unsafe to safe,       *)
(* deactivating the corresponding warnings.                                      *)
(*********************************************************************************)
IncreaseFrontCarGap == /\ cc            = "on"
                       /\ engine        = "on"
                       /\ frontCarGap   > safe
                       /\ gasPedal      = "unpressed"
                       /\ lever         = 0 
                       /\ IF frontCarGap = 3
                            THEN /\ visualWarn'   = "off" 
                            ELSE /\ visualWarn'   = "on"  
                       /\ acousticWarn' = "off"
                       /\ frontCarGap'  = frontCarGap - 1 
                       /\ UNCHANGED<<brakePedal, cc, desiredLimit, desiredSpeed, 
                                     engine, gasPedal, lever, sl, slWarn, speed>>

(*********************************************************************************)
(* Increases current speed (in one unit) until the maximum speed is achieved or  *)
(* until speed limit is reached as long as speed limit function is activated.    *)
(*********************************************************************************)
IncreaseSpeed == /\ brakePedal    = "unpressed"\*
                 /\ \/ /\ cc      = "off" 
                       /\ sl      = "off"
                       /\ speed   < maxSpeed
                    \/ /\ cc      = "off"
                       /\ sl      = "on"
                       /\ speed   < desiredLimit
                    \/ /\ cc      = "on"
                       /\ sl      = "off"
                       /\ speed   >= desiredSpeed
                       /\ speed   < maxSpeed
                 /\ engine        = "on"
                 /\ lever         = 0
                 /\ gasPedal'     = "pressed"
                 /\ speed'        = speed + speedVariation
                 /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                               desiredSpeed, engine, frontCarGap, lever, sl, 
                               slWarn, visualWarn>>
                    
(*********************************************************************************)
(* Nothing changes.                                                              *)
(*********************************************************************************)                        
NothingChanges == /\ brakePedal    = "unpressed"
                  /\ gasPedal      = "unpressed"
                  /\ lever         = 0
                  /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                                desiredSpeed, engine, frontCarGap, gasPedal, 
                                lever, sl, slWarn, speed, visualWarn>>


(*********************************************************************************)
(* Releases brake pedal right after being pressed unless it keeps breaking.      *)
(*********************************************************************************)
ReleaseBrakePedal == /\ brakePedal    = "pressed"
                     /\ engine        = "on"
                     /\ gasPedal      = "unpressed"
                     /\ lever         = 0
                     /\ brakePedal'   = "unpressed"
                     /\ UNCHANGED<<acousticWarn, cc, desiredLimit, desiredSpeed, 
                                   engine, frontCarGap, gasPedal, lever, sl, 
                                   slWarn, speed, visualWarn>>

(*********************************************************************************)
(* Releases gas pedal right after speed increasement unless it keeps increasing  *)
(* speed.                                                                        *)
(*********************************************************************************)
ReleaseGasPedal == /\ brakePedal    = "unpressed"
                   /\ engine        = "on"
                   /\ gasPedal      = "pressed"
                   /\ lever         = 0
                   /\ gasPedal'     = "unpressed" 
                   /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                                 desiredSpeed, engine, frontCarGap, lever, sl, 
                                 slWarn, speed, visualWarn>>
                  
(*********************************************************************************)
(* Lever goes to it's neutral state after being manipulated.                     *)
(*********************************************************************************)         
TurnLever0 == /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         /= 0
              /\ lever'        = 0
              /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                            desiredSpeed, engine, frontCarGap, gasPedal, sl, 
                            slWarn, speed, visualWarn>>
          
(*********************************************************************************)
(* Activates cruise control.                                                     *)
(*********************************************************************************)            
TurnLever1 == /\ cc              = "off"
              /\ brakePedal      = "unpressed"
              /\ engine          = "on"
              /\ gasPedal        = "unpressed"
              /\ lever           = 0
              /\ sl              = "off"
              /\ \/ desiredSpeed > none
                 \/ speed        > stopped
              /\ acousticWarn'   = "off"
              /\ cc'             = "on"
              /\ frontCarGap'    = safe
              /\ lever'          = 1
              /\ visualWarn'     = "off"
              /\ IF desiredSpeed = none 
                   THEN /\ desiredSpeed' = speed
                        /\ speed'        = speed
                   ELSE /\ desiredSpeed' = desiredSpeed 
                        /\ ApproachesDesiredSpeed
              /\ UNCHANGED<<brakePedal, desiredLimit, engine, gasPedal, sl, 
                            slWarn>>
              
(*********************************************************************************)
(* Increases desired speed, desired limit or equals desired speed to current     *)
(* speed depending on the cc, sl, or cc and sl states.                           *)
(*********************************************************************************)
TurnLever2 == /\ brakePedal    = "unpressed"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ lever'        = 2
              /\ \/ /\ cc            = "on"
                    /\ desiredSpeed  < maxSpeed
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = desiredSpeed + speedVariation
                 \/ /\ cc            = "off"
                    /\ desiredLimit  < maxSpeed
                    /\ sl            = "on"
                    /\ desiredLimit' = desiredLimit + speedVariation
                    /\ desiredSpeed' = desiredSpeed
                 \/ /\ cc            = "off"
                    /\ speed         > stopped 
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = speed
              /\ UNCHANGED<<acousticWarn, brakePedal, cc, engine, frontCarGap, 
                            gasPedal, sl, slWarn, speed, visualWarn>>
                    

(*********************************************************************************)
(* Decreases desired speed, desired limit or equals desired speed to current     *)
(* speed depending on the cc, sl, or cc and sl states.                           *)
(*********************************************************************************)
TurnLever3 == /\ brakePedal    = "unpressed"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ lever'        = 3
              /\ \/ /\ cc            = "on"
                    /\ desiredSpeed  > minSpeed
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = desiredSpeed - speedVariation
                 \/ /\ cc            = "off"
                    /\ desiredLimit  > minSpeed
                    /\ sl            = "on"
                    /\ desiredLimit - speedVariation >= speed
                    /\ desiredLimit' = desiredLimit - speedVariation
                    /\ desiredSpeed' = desiredSpeed
                 \/ /\ cc            = "off"
                    /\ speed         > stopped 
                    /\ sl            = "off"
                    /\ desiredLimit' = desiredLimit 
                    /\ desiredSpeed' = speed
              /\ UNCHANGED<<acousticWarn, brakePedal, cc, engine, 
                               frontCarGap, gasPedal, sl, slWarn, speed, 
                               visualWarn>>
                               
(*********************************************************************************)
(* Deactivates cruise control or speed limit function.                           *)
(*********************************************************************************)
TurnLever4 == /\ brakePedal    = "unpressed"
              /\ \/ cc            = "on"
                 \/ sl            = "on"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ acousticWarn' = "off"
              /\ cc'           = "off"
              /\ frontCarGap'  = none
              /\ lever'        = 4   
              /\ sl'           = "off"
              /\ slWarn'       = "off"
              /\ visualWarn'   = "off"
              /\ UNCHANGED<<brakePedal, desiredLimit, desiredSpeed, engine, 
                            gasPedal, speed>>

(*********************************************************************************)
(* Activates or deactivates speed limit depending on the actual state.           *)
(*********************************************************************************)
TurnLever5 == /\ brakePedal    = "unpressed"
              /\ cc            = "off"
              /\ engine        = "on"
              /\ gasPedal      = "unpressed"
              /\ lever         = 0
              /\ speed         <= desiredLimit
              /\ lever'        = 5
              /\ \/ /\ sl      = "on"
                    /\ sl'     = "off"
                    /\ slWarn' = "off"
                 \/ /\ sl      = "off"
                    /\ sl'     = "on"
                    /\ slWarn' = "on" 
              /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredLimit, 
                            desiredSpeed, engine, frontCarGap, gasPedal, speed, 
                            visualWarn>>

(*********************************************************************************)
(* Turn engine off.                                                              *)
(*********************************************************************************)
TurnEngineOff == /\ brakePedal    = "unpressed"
                 /\ engine        = "on"
                 /\ gasPedal      = "unpressed"
                 /\ speed         = stopped
                 /\ acousticWarn' = "off"
                 /\ cc'           = "off"
                 /\ desiredLimit' = none
                 /\ desiredSpeed' = none
                 /\ engine'       = "off"
                 /\ frontCarGap'  = none
                 /\ lever'        = 0
                 /\ sl'           = "off"
                 /\ slWarn'       = "off"
                 /\ speed'        = stopped
                 /\ UNCHANGED<<brakePedal, gasPedal, visualWarn>>

(*********************************************************************************)
(* Turn engine on.                                                               *)
(*********************************************************************************)
TurnEngineOn == /\ brakePedal    = "unpressed"
                /\ cc            = "off"
                /\ engine        = "off"
                /\ gasPedal      = "unpressed"
                /\ lever         = 0
                /\ sl            = "off"
                /\ desiredLimit' = none
                /\ engine'       = "on"
                /\ lever'        = 0
                /\ speed'        = 1
                /\ UNCHANGED<<acousticWarn, brakePedal, cc, desiredSpeed, 
                              frontCarGap, gasPedal, sl, slWarn, visualWarn>>


                          (*##########################*)


(*********************************************************************************)
(* Defines the next state.                                                       *)
(*********************************************************************************)                        
Next == \/ Brake
        \/ DecreaseFrontCarGap
        \/ DecreaseSpeed
        \/ EqualsDesiredSpeed
        \/ IncreaseFrontCarGap
        \/ IncreaseSpeed
        \/ NothingChanges
        \/ ReleaseBrakePedal
        \/ ReleaseGasPedal
        \/ TurnLever0
        \/ TurnLever1
        \/ TurnLever2
        \/ TurnLever3 
        \/ TurnLever4
        \/ TurnLever5
        \/ TurnEngineOff
        \/ TurnEngineOn


                          (*##########################*)
                          
                          
 \*DÚVIDAS SCS11, turn lever 3 
 \* colocar unchangeds
 \* formular props temporais                          
(*********************************************************************************)
(* SCS-1 -> check! MAS PERGUNTAR AO PROF                                         *)
(* SCS-2 -> check! MAS PERGUNTAR AO PROF                                         *)
(* SCS-3 -> check!                                                               *) 
(* SCS-4 -> check SCSA!                                                          *)
(* SCS-5 -> check SCSA!                                                          *)
(* SCS-6 -> check SCSB!                                                          *)
(* SCS-7 -> check SCSA!                                                          *)
(* SCS-8 -> check SCSA!                                                          *)
(* SCS-9 -> check SCSB!                                                          *)
(* SCS-10 -> check SCSB!                                                         *)
(* SCS-A -> check! MAS PERGUNTAR AO PROF PQ NAO SE SABE FAZER ASSERT             *)
(* SCS-B -> check! MAS PERGUNTAR AO PROF PQ NAO SE SABE FAZER ASSERT             *)
(* SCS-11 -> check! MAS PERGUNTAR AO PROF PQ NAO SE SABE FAZER ASSERT 'BEM'      *)
(* SCS-12 -> check!                                                              *)
(* SCS-13 -> check!                                                              *) 
(* SCS-14 -> check! MAS PERGUNTAR AO PROF PQ NAO SE SABE FAZER ASSERT            *)
(* SCS-15 -> not hap                                                             *)
(* SCS-16 -> check!                                                              *)
(* SCS-17 -> check!                                                              *)
(* SCS-18 -> check! MAS PERGUNTAR AO PROF PQ NAO SE SABE FAZER ASSERT            *)
(* SCS-19 -> check! MAS PERGUNTAR AO PROF PQ NAO SE SABE FAZER ASSERT            *)
(* SCS-20 -> won't be specified.                                                 *)
(* SCS-21 -> won't be specified.                                                 *)
(* SCS-22 -> won't be specified.                                                 *)
(* SCS-23 -> won't be specified.                                                 *)
(* SCS-24 -> won't be specified.                                                 *)
(* SCS-25 -> check!                                                              *)
(* SCS-26 -> check!                                                              *)
(* SCS-27 -> won't be specified.                                                 *)
(* SCS-28 -> won't be specified.                                                 *)
(* SCS-29 -> check! MAS PERGUNTAR AO PROF                                        *)
(* SCS-30 -> check!                                                              *)
(* SCS-31 -> check! MAS PERGUNTAR AO PROF                                        *)
(* SCS-32 -> check!                                                              *)
(* SCS-33 -> won't be specified.                                                 *)
(* SCS-34 -> won't be specified.                                                 *)
(* SCS-35 -> check! MAS PERGUNTAR AO PROF                                        *)
(* SCS-36 -> won't be specified.                                                 *)
(* SCS-37 -> won't be specified.                                                 *)
(* SCS-38 -> won't be specified.                                                 *)
(* SCS-39 -> won't be specified.                                                 *)
(* SCS-40 -> won't be specified.                                                 *)
(* SCS-41 -> won't be specified.                                                 *)
(* SCS-42 -> won't be specified.                                                 *)
(* SCS-43 -> won't be specified.                                                 *)
(*********************************************************************************)

===========================================================================================================
\* Modification History
\* Last modified Thu Jan 09 18:46:22 WET 2020 by ricardo