%% Wolf, goat and cabbage problem. From Wikipedia:
%%
%% "Once upon a time a farmer went to a market and purchased a wolf, a goat, and a cabbage.
%% On his way home, the farmer came to the bank of a river and rented a boat.
%% But crossing the river by boat, the farmer could carry only himself and a single one of his purchases: the wolf, the goat, or the cabbage.
%% If left unattended together, the wolf would eat the goat, or the goat would eat the cabbage.
%%
%% The farmer's challenge was to carry himself and his purchases to the far bank of the river, leaving each purchase intact. How did he do it?”

%% Parameters.
enum PASSENGER = {Farmer, Wolf, Goat, Cabbage};
enum LOC = {bankA, bankB};

int: maxstep = 10;
set of int: STEP0 = 0..maxstep;
set of int: STEP = 1..maxstep;

%% Decision variables.
array[STEP0] of var LOC: farmerLoc;
array[STEP0] of var LOC: wolfLoc;
array[STEP0] of var LOC: goatLoc;
array[STEP0] of var LOC: cabbageLoc;

% Helper type: two-dimensional array of the unknown locations.
array[PASSENGER, STEP0] of var LOC: loc =
    array2d(PASSENGER, STEP0,
            farmerLoc ++ wolfLoc ++ goatLoc ++ cabbageLoc);

var STEP: end;

%% Constraints.
% The farmer arrives at the river with his purchases.
constraint forall(p in PASSENGER)(loc[p,0] = bankA);
% The farmer crosses the river with his purchases after end steps.
constraint forall(p in PASSENGER, s in STEP where s >= end)(loc[p,s] = bankB);
constraint end <= maxstep;

% If the location of a passenger changes from one river bank to the other,
% so should change the location of the farmer too.
% Note that STEP is 1..maxtep allowing us to access s-1.
predicate passenger_moves(var PASSENGER: p, var STEP: s) =
        let { var LOC: farmer_last_pos = loc[Farmer,s-1];
              var LOC: farmer_new_pos = loc[Farmer,s];
              var LOC: last_pos = loc[p,s-1];
              var LOC: new_pos = loc[p,s]; } in
              last_pos != new_pos -> farmer_last_pos = last_pos /\ farmer_new_pos = new_pos;
% Constrain all passengers (farmer and his purchases).
constraint forall(p in PASSENGER, s in STEP)(passenger_moves(p, s));

% Never leave the wolf with the goat or the goat with the cabbage alone.
constraint forall(s in STEP)(wolfLoc[s] = goatLoc[s] \/ goatLoc[s] = cabbageLoc[s]
                             -> farmerLoc[s] = goatLoc[s]);

% The farmer can carry only himself and a single one of his purchases.
% If the location of the farmer changes, at most one purchase can change its location as well.
constraint forall(s in STEP)
                 (farmerLoc[s-1] != farmerLoc[s] -> sum(p in PASSENGER where p != Farmer)
                                                       (loc[p,s-1] != loc[p,s]) <= 1);

%% Objective.
solve minimize end;

%% Output.
% Our emojis.
array[PASSENGER] of string: emoji = ["👨‍🌾","🐺","🐐","🥬"] ::output_only;

output
[ "Step \(s): " ++ % step prefix
  show([ emoji[p] | p in PASSENGER where fix(loc[p,s]) = bankA ]) ++
  " <-> " ++
  show([ emoji[p] | p in PASSENGER where fix(loc[p,s]) = bankB ]) ++
  "\n"
  | s in 1..fix(end) ]; % generator
