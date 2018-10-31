Directly from the Github page :
--------------------------------
Informal Spec :
--------------------------------

Nodes are compartment that contains molecules M. Total N nodes. 0/1 means
whether molecule is presnt or not.

Edges represent vesicles that are going out to fuse to another
compartment. Allowed things should be subset molecules that are present at
the nodes.

Steady State :
------------------------------
The System should have to be in steady state. I.e inflow and outflow of
different type of molecules should be same.
Condition Needs To be checked : Each molecule leaving should come back to
source node in a cycle.

Representation :
--------------------------
 Half of Molecules represents vsnares and other halfs are t snares. in 2 *
 N NBIt long molecule configuration First halfs are v snares and rest are
 t snares.

 Fusion Rules :
 ------------------------------

 In order to fusion to occur v snares present at edge should find the
 corresponding t snares at the target node. That is driven by the
 FriendMatrix v * t matrix : Represnts which t snares are required in order
 to fusion to happen. And all tsnares required for the fusion should be in
 on state based on onOff Matrix : which states which t snares are in active
 phase at any node. At least one vsnare should pass all constraints and
 allow fusion to occur. Multiple can.

 Other constraine is that the tsnares that are required for fusion have not
 to be present at edge. Else that vsnare will not be considered for a
 candidate for the fusion. For source compartment also, those t snares have
 to be absent or present but are surely off (a 0 Onoff matrix).

# cbmc-vts
