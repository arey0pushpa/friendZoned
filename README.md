
# Welcome to FrienZoned Model Of Vesicular Traffic System!
=======================

The Biology model of Trafficing happens at cell level. This model is complete vsnare and tsnare analogy of what happens in real cell. 

  ![](http://www.zoology.ubc.ca/~berger/B200sample/unit_8_protein_processing/images_unit8/14_20.jpg)

     Complete Description Of the PROJECT

> Nodes are compartment that contains molecules M. Total N nodes. 0/1 means whether molecule is presnt or not.

>  Edges represnt vesicles that are going out to fuse to another compartment. 
> Allowed things should be subset moleculs that are presnt at the nodes. The System should have to be in steady state. I.e inflow and outflow of different type of molecules should be same. Half of Molecules represnts vsnares and other halfs are t snares. in 20 NBIt long molecule configuration 
>  First halfs are v snares and rest are t snares. 0011 00 is first half 11 is second half. 

>  In order to fusion to occur v snares present at edge should find the corresponding t snares at the target node. 
>  That is driven by the FriendMatrix v * t matrix : Represnts which t snares are required in order to fusion to happen. 
>  And all tsnares required for the fusion should be in on state based on onOff Matrix : which states which t snares are
  in active phase at any node. 
>   At least one vsnare should pass all constraints and allow fusion to occur. Multiple can.
>   Other constraine is that the  tsnares that are required for fusion have not to be present at edge. 
>   Else that vsnare will not be considered for a candidate for the fusion. For source compartment also, those t snares have to be absent or present but are surely off (a 0 Onoff matrix).  

  I'm finding whether there is an assignment possible for the given graph or not. And then going to use it in future other special properties checks. 


Wiki
------------

This is a model of Vesiclular Traffic system in cells. I'm using model checkers to come up with an assignment that follows certain rules and contraints.  

Found a bug?
------------
Just Take authority and change. 

Contributing
------------

We welcome pull requests from Human , Aliens , Advanced Computers , Dumb circuits, Toys , Animals , Virus , Bacterias so feel ashamed for any contribution. 


### Usage

You can create an instance of ParseServer, and mount it on a new or existing Express website:


```js

// For Ubuntu diretly just 
# apt-get install cbmc

// Others Follow Cprover Link

http://www.cprover.org/cbmc/

# In Order To Run :
// First check from file the line number of dynamic code. I have commented which one is dynamic.
// Forexample in friendZoned.c Line No. 181 ,185,2985,300 are dynamic.  So you have to provide total unwindings to the loop.
# cbmc filename.c --show-loops

// There are parts that are dynamic in the code s just write basic --unwindset
//  c::main.loop_number:total_number_of_unwindings
# cbmc filename.c --unwindset c::main.0:10,c::main.1:20  --no-unwinding-assertions 

// For fiveVTSnare.c loop Number 7,8,10,11 are the ones 
# cbmc filename.c --unwindset c::main.7:5,c::main.8:5,c::main.10:5,c::main.11:5 
   --no-unwinding-assertions 

```

License
-------

The LSD Clause

Copyright (c) 2016, *^&$$12)+
All rights UN-reserved.


1. Redistributions of source code may be injurious to health.

2. Redistributions in binary form may expose you to radioactive radiations. 

THIS SOFTWARE IS FREE OF COST LIABILITY TO WHOLE UNIVERSE. THE ONLY POSSIBLE WAY TO CONTIBUTE TO IMPRVE THE CURRENT SITUATION IS TO TAKE RESPONSIBILTY OF ABOVE AND CHANGE IT AS MUCH IS POSSIBLE. 
