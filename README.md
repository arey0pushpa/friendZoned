# friendZoned
The Biology model of Trafficing happens at cell level. This model is complete vsnare and tsnare analogy of what happens in real cell. 

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
