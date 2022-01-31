# Speed Control System (SCS) Modelling

The automotive domain is full of critical systems/situations where a formal specification is absolutly essential. The goal of this project was to model the Speed Control System behavior of a car. The specification considers multiple factors of which, speed value, speed limits, lever position, brake pedal, are a few.


## Tools

[![alt text](https://lamport.azurewebsites.net/tla/splash_small.png)](https://lamport.azurewebsites.net/tla/tla.html)


## Setup

In order to execute [SCS.tla](SCS.tla) specification in TLA+, one only needs to download the ToolBox from [here](https://tla.msr-inria.inria.fr/tlatoolbox/products/). After extracting the .zip file, the resulting folder will contain a file named "toolbox" which launches the tool itself.


## Abstract

In essence, we define multiple **variables** to which we assign multiple values. The content of each of these variables changes according to a given **predicate** that fits the actual state. In another words, given a state, there are one or more actions that can be applied to that state, as long as these action(s) (predicate(s)) match the same given state. There are also **invariants** which are conditional expressions that are constantly compared to the actual state - these assess if there isn't any incompatibility of the state with the existing properties. 

By specifying a model like this, it is then possible to navigate through the existing states and prove that the situations we thought about are indeed achievable. But more important than that is the ability of finding situations we weren't thinking about - this can be found by navigating through the possible states or everytime an invariant is infringed.


## Code explanation

* Variables
    + acousticWarn - An audible warning that is activated when the distance to an obstacle in front of the car is critical. It can be on or off. 
    + brakePedal - The position of the brake pedal. It can be pressed or unpressed. 
    + cc - Indicates if the cruise control is on or off. 
    + desiredLimit -  
    + desiredSpeed - 
    + engine - The state of the engine, which is either on or off.
    + frontCarGap - The distance to an obstacle in front of the car is 1 (none), 2 (safe), 3 (unsafe) or 4 (critical).
    + gasPedal - The position of the gas pedal. It can be pressed or unpressed.
    + lever - Indicates he different positions of the lever:
        - 1 - Activates cruise control.
        - 2 - Increases desired speed, desired limit or equals desired speed to current speed depending on the cc, sl, or cc and sl states. 
        - 3 - Decreases desired speed, desired limit or equals desired speed to current speed depending on the cc, sl, or cc and sl states.
        - 4 - Deactivates cruise control or speed limit function.
        - 5 - Activates or deactivates speed limit depending on the actual state.
    + sl - Indicates if the speed limit system is on or off.
    + slWarn - An visible warning that is activated when the speed limit is activated. It can be on or off.
    + speed - The different possible speeds: 1 (stopped), 2 (slow), 3(medium) or 4 (fast).
    + visualWarn - An audible warning that is activated when the distance to an obstacle in front of the car is critical. It can be on or off.

* Predicates
    + Brake - The car brakes and reduces current speed (in one unit).
    + DecreaseFrontCarGap - Decreases front car gap from safe to unsafe or from unsafe to critical, activating the corresponding warnings.
    + DecreaseSpeed - Decreases current speed (in one unit).
    + EqualsDesiredSpeed - Predicate that is continuously called since when the lever is turned to 1 untill speed equals desired speed.
    + IncreaseFrontCarGap - Increases front car gap from critical to unsafe or from unsafe to safe, deactivating the corresponding warnings.
    + IncreaseSpeed - Increases current speed (in one unit) until the maximum speed is achieved or until speed limit is reached as long as speed limit function is activated.
    + NothingChanges - Nothing changes.
    + ReleaseBrakePedal - Releases brake pedal right after being pressed unless it keeps breaking.
    + ReleaseGasPedal - Releases gas pedal right after speed increasement unless it keeps increasing speed.
    + TurnLever0 - Lever goes to it's neutral state after being manipulated.
    + TurnLever1 - Activates cruise control.
    + TurnLever2 - Increases desired speed, desired limit or equals desired speed to current speed depending on the cc, sl, or cc and sl states.
    + TurnLever3 - Decreases desired speed, desired limit or equals desired speed to current speed depending on the cc, sl, or cc and sl states.
    + TurnLever4 - Deactivates cruise control or speed limit function.
    + TurnLever5 - Activates or deactivates speed limit depending on the actual state.
    + TurnEngineOff - Turn engine off.  
    + TurnEngineOn - Turn engine on.

## Execution

This section shows how to run the specification in the ToolBox and other aspects metioned above.


### Running the [SCS.tla](SCS.tla) file in the ToolBox 

![Normal execution](.media/noerrorsexecution.gif)


### Changing and running [SCS.tla](SCS.tla) file in the ToolBox forcing it to show a conterexample

![Execution with counterexample](.media/executionwitherrors.gif)



