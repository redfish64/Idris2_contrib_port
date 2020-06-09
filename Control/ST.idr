module Control.ST

--import Control.IOExcept
--import Language.Reflection.Utils

import public Data.Fuel

%default total

infix 5 :::

{- A resource is a pair of a label and the current type stored there -}
public export
data Resource : Type where
     MkRes : label -> Type -> Resource

export
data Var = MkVar -- Phantom, just for labelling purposes

resfoo : Resource
resfoo = MkRes MkVar Int

--%error_reverse
public export
(:::) : Var -> Type -> Resource
(:::) = MkRes

{- Contexts for holding current resources states -}
namespace Resources
  public export
 data Resources : Type where
       Nil : Resources
       (::) : Resource -> Resources -> Resources

  public export
  (++) : Resources -> Resources -> Resources
  (++) [] res = res
  (++) (re :: res1) res2 = re :: res1 ++ res2

ressfoo : Resources
ressfoo = (MkRes MkVar String) :: Nil


{- Proof that a label has a particular type in a given context -}
public export
data InState : (x : Var) -> Type -> Resources -> Type where
     [search x]
     Here : InState lbl t (MkRes lbl t :: res)
     There : InState lbl t res -> InState lbl t (re :: res)

{- Update an entry in a context with a new state -}
public export
updateRes : (res : Resources) ->
             InState lbl t res -> Type -> Resources
updateRes (MkRes lbl _ :: res) Here val = (MkRes lbl val :: res)
updateRes (re :: res) (There iis) ty = re :: updateRes res iis ty

{- Remove an entry from a context -}
public export
drop : (res : Resources) -> (is : InState lbl st res) ->
       Resources
drop (MkRes lbl st :: res) Here = res
drop (re :: res) (There iis) = re :: drop res iis

{- Proof that a resource is in resources -}
public export
data ElemRes : Resource -> Resources -> Type where
     HereRes : ElemRes re (re :: res)
     ThereRes : ElemRes re res -> ElemRes re (othRe :: res)

public export --%error_reduce
dropEl : (res: Resources) -> ElemRes re res -> Resources
dropEl (re :: rres) HereRes = rres
dropEl (othRe :: rres) (ThereRes iis) = othRe :: dropEl rres iis

{- Proof that a variable name is in a context -}
public export
data VarInRes : Var -> Resources -> Type where
     VarHere   : VarInRes v (MkRes v vt :: rres)
     VarThere  : VarInRes v res -> VarInRes v (ov :: res)

virFoo : VarInRes (MkVar) ((MkRes MkVar String) :: Nil)
virFoo = VarHere

StrIntRes : Resources
StrIntRes = ((MkRes MkVar String) :: (MkRes MkVar Int) :: Nil)

VirFooType : Type
VirFooType = VarInRes (MkVar) StrIntRes

virFooType2 : Var -> Type
virFooType2 a = VarInRes a StrIntRes

virFoo1 : VirFooType
virFoo1 = VarHere

virFoo2 : virFooType2 MkVar
virFoo2 = VarHere

virFoo3 : virFooType2 MkVar
virFoo3 = VarThere (VarHere) 

-- virFoo2 : VarInRes (MkVar) ((MkRes MkVar String) :: (MkRes MkVar Int) :: Nil)
-- virFoo2 = VarHere
-- virFoo2 = VarThere (VarHere) 

--removes a var from resources and returns the remainder
public export --%error_reduce
dropVarIn : (res: Resources) -> VarInRes v res -> Resources
dropVarIn (_ :: rres) VarHere = rres
dropVarIn (othRe :: res) (VarThere iis) = othRe :: dropVarIn res iis

dropfoo : Resources
dropfoo = dropVarIn StrIntRes virFoo3

--list of values of heterogenious types
public export
data Composite : List Type -> Type where
     CompNil : Composite []
     CompCons : (x : ty) -> Composite tys -> Composite (ty :: tys)

--this is just a list of Var (a phantom type). The type of the VarList
--is a list of types, however
namespace VarList
  public export
  data VarList : List Type -> Type where
       Nil : VarList []
       (::) : Var -> VarList ts -> VarList (t :: ts)

  public export
  mkRes : {tys : List Type} -> VarList tys -> Resources
  mkRes [] = []
  mkRes {tys = t :: ts} (v :: vs) = (v ::: t) :: mkRes vs


foovarlist : VarList [ Int, String ]
foovarlist = [ MkVar, MkVar ]
--foovarlist = MkVar :: MkVar :: Nil --same,same

{- Proof that a list of resources is a subset of another list -}
--note that the length of subres is always the same as the resources it represents
public export
data SubRes : Resources -> Resources -> Type where
     SubNil : SubRes [] []
     Skip : SubRes xres yres -> SubRes xres (yre :: yres)
     --tim: it seems that elRe can only be HereRes
     -- takes a proof that re is in yres, a subres where xres is in yres without
     -- re, and returns a subres of xres with re
     InRes : (elRe : ElemRes re yres) -> SubRes xres (dropEl yres elRe) ->
              SubRes (re :: xres) yres

{- proof that a Resources is a SubRes of itself -}
%hint
public export
subResId : {xs : _ } -> SubRes xs xs
subResId {xs = []} = SubNil
subResId {xs = (x :: xs)} = InRes HereRes subResId

{- proof that an empty Resource is a SubRes of anything -}
public export
subResNil : {xs : _ } -> SubRes [] xs
subResNil {xs = []} = SubNil
subResNil {xs = (x :: xs)} = Skip subResNil

{- Proof that every variable in the list appears once in the context -}
public export
data VarsIn : List Var -> Resources -> Type where
     VarsNil : VarsIn [] []
     SkipVar : VarsIn v res -> VarsIn v (re :: res)
     InResVar : (vir : VarInRes v res) -> VarsIn vars (dropVarIn res vir) ->
                 VarsIn (v :: vars) res

FooVarIn : Var -> Var -> Type
FooVarIn a b = VarsIn [ a, b ] [MkRes b Int , MkRes a String ]

-- fooVarIn : FooVarIn MkVar MkVar
-- fooVarIn = InResVar ?a ?b

FooVarIn2 : Var -> Var -> Type
FooVarIn2 a b = VarsIn [ a, b ] [MkRes b Int , MkRes a String ]

public export
Uninhabited (ElemRes x []) where
  uninhabited HereRes impossible
  uninhabited (ThereRes _) impossible

{- tim: Seems to replace the SubRes in xres with newRes, returning the new resources -}
public export --%error_reduce
updateWith : (newRes : Resources) -> (xres : Resources) ->
             SubRes yres xres -> Resources
-- At the end, add the ones which were updated by the subctxt
updateWith new [] SubNil = new 
updateWith new [] (InRes elRe sr) = absurd elRe
-- Don't add the ones which were consumed by the subctxt
updateWith [] (re :: res) (InRes elRe remSubRes)
    = updateWith [] (dropEl (re :: res) elRe) remSubRes
-- A new item corresponding to an existing thing
updateWith (nre :: nres) (xre :: xres) (InRes elRe remSubRes)
    = nre :: updateWith nres (dropEl (xre :: xres) elRe) remSubRes
updateWith new (xre :: xres) (Skip remSubRes) = xre :: updateWith new xres remSubRes

rebldPrf: {new,yres : Resources} -> {subRes : SubRes xres yres} -> updateWith new (yre :: yres) (Skip subRes) = (yre :: updateWith new yres subRes)
rebldPrf {new = []} {  yres = []} = Refl
rebldPrf {new = (x :: y)} {  yres = []} = Refl
rebldPrf {new = []} {    yres = (x::y)} = Refl
rebldPrf {new = (z :: w)} {    yres = (x::y)} = Refl

public export
getVarType : (res : Resources) -> VarInRes v res -> Type
getVarType ((MkRes v ty) :: rres) VarHere = ty
getVarType (othRe :: rres) (VarThere rvir) = getVarType rres rvir

public export
getCombineType : {res : Resources} -> VarsIn vars res -> List Type
getCombineType VarsNil = []
getCombineType {res} (InResVar vir rvir) = getVarType res vir :: getCombineType rvir
getCombineType (SkipVar rvir) = getCombineType rvir

public export
dropCombined : {res : Resources} -> VarsIn vs res -> Resources
dropCombined {res = []} VarsNil = []
dropCombined {res} (InResVar vir rvir) = dropCombined rvir
dropCombined {res = (re :: rres)} (SkipVar rvir) = re :: dropCombined rvir

{- Tim : strips off the first var in VarsIn, and places within it the types of the rest
   of the vars, deleting them. Is this a bug? It's throwing away its own type.
   
   Any resource in res that is not part of VarsIn gets to stay in the result.
   
   It's very subtle. It only accepts a VarsIn and recursively calls itself. So
   it seems at first glance that it wouldn't compile, because what if it's passed
   SkipVar NilVar. There is no case for NilVar, so when it recursively called itself
   it would not have a case to go to. 
   
   But SkipVar takes the same vars as what it contains, so:
   
   SkipVar : VarsIn v res -> VarsIn v (re :: res)
   
   and 
   
   VarsNil : VarsIn [] []
   
   means that SkipVar has the type VarsIn [] res.
   
   Since this only takes VarsIn (v :: vs), it  won't accept SkipVar NilVar
   
    -}
public export
combineVarsIn : {fvar : Var} -> (res : Resources) -> VarsIn (fvar :: vs) res -> Resources
combineVarsIn {fvar} res (InResVar vir rvi)
     = ((fvar ::: Composite (getCombineType rvi)) :: dropCombined (InResVar vir rvi))
combineVarsIn (re :: rres) (SkipVar rvi) = re :: combineVarsIn rres rvi

namespace combfoo
  resMkr : Var -> Var -> Resources
  resMkr a b = [MkRes a String, MkRes b Int]
  
  virMkr : {v1,v2 : Var} -> (VarInRes v1 (resMkr v1 v2), VarInRes v2 (resMkr v1 v2))
  virMkr = (VarHere, VarThere VarHere)
  
  -- varsIn1 : {v1,v2 : Var} -> VarsIn [v2] (resMkr v1 v2)
  -- varsIn1 = 
  --   let (vir1,vir2) = virMkr
         
  --   in 
  --     InResVar vir2 VarsNil)
    
  -- v2 in the second elem of a Resources  
  varInRes2 : {v1,v2 : Var} -> VarInRes v2 ((MkRes v1 Int) :: (MkRes v2 String) :: Nil)
  varInRes2 = 
    let 
        vir2 = the (VarInRes v2 ((MkRes v2 String) :: Nil)) VarHere
        vir = VarThere vir2
    in 
      vir
      
  varsIn0 : {v1,v2 : Var} -> VarsIn [] ((MkRes v1 Int) :: (MkRes v2 String) :: Nil)
  varsIn0 = SkipVar $ SkipVar VarsNil
  
  varsIn1 : {v1,v2 : Var} -> VarsIn [v1] ((MkRes v1 Int) :: (MkRes v2 String) :: Nil)
  varsIn1 = InResVar VarHere $ SkipVar VarsNil
  
  varsIn2 : {v1,v2 : Var} -> VarsIn [v2] ((MkRes v1 Int) :: (MkRes v2 String) :: Nil)
  varsIn2 = SkipVar $ InResVar VarHere VarsNil

  public export
  foocomb : Resources 
  foocomb = 
      combineVarsIn ((MkRes MkVar Int) :: (MkRes MkVar String) :: Nil) (InResVar VarHere $ SkipVar VarsNil)

  -- tim: pretty cool, it won't match an empty InVars, even though there is a case for it, 
  -- combineVarsIn (re :: rres) (SkipVar rvi) = re :: combineVarsIn rres rvi
  -- because the inner one can't match  (see notes for combineVarsIn)
  -- 
  -- public export
  -- foocomb1 : Resources 
  -- foocomb1 = 
  --     combineVarsIn ((MkRes MkVar Int) :: (MkRes MkVar String) :: Nil) (SkipVar $ SkipVar VarsNil)


namespace Env
  public export
  
  {- Associates a value with a type -}
  data Env : Resources -> Type where
       Nil : Env []
       (::) : ty -> Env res -> Env ((lbl ::: ty) :: res)

  public export
  (++) : Env res1 -> Env res2 -> Env (res1 ++ res2)
  (++) [] res2 = res2
  (++) (re1 :: res1) res2 = re1 :: res1 ++ res2

{- Gets the value for a particular var in a Resource -}
lookupEnv : InState lbl ty res -> Env res -> ty
lookupEnv Here (re :: res) = re
lookupEnv (There p) (re :: res) = lookupEnv p res

updateEnv : (prf : InState lbl ty res) -> Env res -> ty' ->
            Env (updateRes res prf ty')
updateEnv Here (x :: xs) val = val :: xs
updateEnv (There p) (x :: xs) val = x :: updateEnv p xs val

dropVal : (prf : InState lbl st res) -> Env res -> Env (drop res prf)
dropVal Here (x :: xs) = xs
dropVal (There p) (x :: xs) = x :: dropVal p xs

envElem : ElemRes x xs -> Env xs -> Env [x]
envElem HereRes (x :: xs) = [x]
envElem (ThereRes p) (x :: xs) = envElem p xs

dropDups : Env xs -> (el : ElemRes x xs) -> Env (dropEl xs el)
dropDups (y :: ys) HereRes = ys
dropDups (y :: ys) (ThereRes p) = y :: dropDups ys p


dropEntry : Env res -> (prf : VarInRes x res) -> Env (dropVarIn res prf)
dropEntry (x :: env) VarHere = env
dropEntry (x :: env) (VarThere y) = x :: dropEntry env y

compfoo : Composite [Int,String]
compfoo = CompCons 1 (CompCons "Foo" CompNil)

dropPrf : (res : Resources) -> (vir : VarInRes v res) -> (rvi : VarsIn xs (dropVarIn res vir)) ->  dropCombined rvi = dropCombined (InResVar vir rvi)
dropPrf [] vir rvi impossible
dropPrf ((MkRes v vt) :: res) VarHere rvi = Refl
dropPrf (re :: res) (VarThere x) rvi = Refl


dropVarsIn : {res : Resources} -> Env res -> (vi : VarsIn vs res) -> Env (dropCombined vi)
dropVarsIn [] VarsNil = []
--dropVarsIn env (InResVar vir rvi) = dropVarsIn (dropEntry env vir) rvi
dropVarsIn env (InResVar vir rvi) = 
  let
     denv = dropEntry env vir
     vvv = dropVarsIn denv rvi
     dvp = dropPrf res vir rvi
     dvs = sym $ dvp
     xxx = rewrite__impl Env dvs vvv
  in
    xxx
dropVarsIn (x :: env) (SkipVar rvi) = x :: dropVarsIn env rvi


getVarEntry : Env res -> (prf : VarInRes v res) -> getVarType res prf
getVarEntry (x :: xs) VarHere = x
getVarEntry (x :: env) (VarThere p) = getVarEntry env p

compProof2 : (res : Resources) -> (vir : VarInRes v res) -> (vi : VarsIn otherVars (dropVarIn res vir)) -> (getVarType res vir :: getCombineType vi) = (getCombineType (InResVar vir vi))
compProof2 [] vir vi impossible
compProof2 ((MkRes var type) :: []) vir vi = Refl

mkComposite : {vs, res : _ } -> Env res -> (prf : VarsIn vs res) -> Composite (getCombineType prf)
mkComposite [] VarsNil = CompNil
mkComposite env (InResVar vir vi) = 
  let 
     cps = sym $ compProof2 res vir vi
  in rewrite__impl Composite cps (CompCons (getVarEntry env vir) $ mkComposite (dropEntry env vir) vi)
mkComposite (x :: env) (SkipVar z) = mkComposite env z

rebuildVarsIn : { vs,res : _ } -> Env res -> (prf : VarsIn (comp :: vs) res) ->
                Env (combineVarsIn res prf)
rebuildVarsIn env (InResVar el p)
     = mkComposite (dropEntry env el) p :: dropVarsIn env (InResVar el p)
rebuildVarsIn (x :: env) (SkipVar p) = x :: rebuildVarsIn env p

{- Some things to make STrans interfaces look prettier -}

infix 6 :->

public export
data Action : Type -> Type where
     Stable : Var -> Type -> Action ty
     Trans : Var -> Type -> (ty -> Type) -> Action ty
     Remove : Var -> Type -> Action ty
     Add : (ty -> Resources) -> Action ty

namespace Stable
  public export --%error_reduce
  (:::) : Var -> Type -> Action ty
  (:::) = Stable

namespace Trans
  public export
  data Trans ty = (:->) Type Type

  public export --%error_reduce
  (:::) : Var -> Trans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st (const st')

namespace DepTrans
  public export
  data DepTrans ty = (:->) Type (ty -> Type)

  public export --%error_reduce
  (:::) : Var -> DepTrans ty -> Action ty
  (:::) lbl (st :-> st') = Trans lbl st st'

public export
or : a -> a -> Either b c -> a
or x y = either (const x) (const y)

public export --%error_reduce
add : Type -> Action Var
add ty = Add (\var => [var ::: ty])

public export --%error_reduce
remove : Var -> Type -> Action ty
remove = Remove

public export --%error_reduce
addIfRight : Type -> Action (Either a Var)
addIfRight ty = Add (either (const []) (\var => [var ::: ty]))

public export --%error_reduce
addIfJust : Type -> Action (Maybe Var)
addIfJust ty = Add (maybe [] (\var => [var ::: ty]))

{- Keeps only Resources in parent that are not in child (of SubRes) -}
public export
kept : {ys : _ } -> SubRes xs ys -> Resources
kept SubNil = []
kept (InRes el rsr) = kept rsr
kept (Skip {yre} p) = yre :: kept p

-- We can only use new/delete/read/write on things wrapped in State. Only an
-- interface implementation should know that a thing is defined as State,
-- so it's the only thing that's able to peek at the internals
public export
data State : Type -> Type where
     Value : ty -> State ty

export
data STrans : (m : Type -> Type) ->
              (ty : Type) ->
              Resources -> (myoutfn : ty -> Resources) ->
              Type where
     Pure : (result : ty) ->
            STrans m ty (out_fn result) out_fn 
     Bind : {a : Type} -> {st2_fn : a -> Resources} -> STrans m a st1 st2_fn ->
            ((result : a) ->
                STrans m b (st2_fn result) st3_fn) ->
            STrans m b st1 st3_fn
     Lift : Monad m => m t -> STrans m t res (const res)
     RunAs : Applicative m => {t : Type} -> {out_res : _ } -> STrans m t in_res (const out_res) ->
             STrans m (m t) in_res (const out_res)

     New : (val : state) ->
           STrans m Var res (\lbl => (lbl ::: state) :: res)
     Delete : (lbl : Var) ->
              (prf : InState lbl st res) ->
              STrans m () res (const (drop res prf))
     DropSubRes : (prf : SubRes ys xs) ->
                  STrans m (Env ys) xs (const (kept prf))

     Split : (lbl : Var) ->
             (prf : InState lbl (Composite vars) res) ->
             STrans m (VarList vars) res
                   (\vs => mkRes vs ++
                            updateRes res prf (State ()))
     Combine : (comp : Var) -> (vs : List Var) ->
               (prf : VarsIn (comp :: vs) res) ->
               STrans m () res
                   (const (combineVarsIn res prf))
     ToEnd : (lbl : Var) ->
             (prf : InState lbl state res) ->
             STrans m () res (const (drop res prf ++ [lbl ::: state]))

     Call : {sub, new_f : _ } -> STrans m t sub new_f -> (res_prf : SubRes sub old) ->
            STrans m t old (\res => updateWith (new_f res) old res_prf)

     Read : (lbl : Var) ->
            (prf : InState lbl ty res) ->
            STrans m ty res (const res)
     Write : (lbl : Var) ->
             (prf : InState lbl ty res) ->
             (val : ty') ->
             STrans m () res (const (updateRes res prf ty'))

namespace Loop
  public export
  data STransLoop : (m : Type -> Type) -> (ty : Type) ->
                    Resources -> (ty -> Resources) -> Type where
       Bind : {a : Type } -> {st2_fn : a -> Resources} -> STrans m a st1 st2_fn ->
              ((result : a) -> Inf (STransLoop m b (st2_fn result) st3_fn)) ->
              STransLoop m b st1 st3_fn
       Pure : (result : ty) -> STransLoop m ty (out_fn result) out_fn

export
dropEnv : Env ys -> SubRes xs ys -> Env xs
dropEnv [] SubNil = []
dropEnv [] (InRes idx rest) = absurd idx
dropEnv (z :: zs) (InRes idx rest)
    = let [e] = envElem idx (z :: zs) in
          e :: dropEnv (dropDups (z :: zs) idx) rest
dropEnv (z :: zs) (Skip p) = dropEnv zs p

keepEnvPrf : (elRe : ElemRes re ys) -> (rsr : SubRes xres (dropEl ys elRe)) -> Env ys -> Env (kept rsr) -> kept (InRes elRe rsr) = kept rsr
keepEnvPrf HereRes rsr x y = Refl
keepEnvPrf (ThereRes z) rsr x y = Refl


-- in rewrite__impl Composite ?cps (CompCons (getVarEntry env vir) $ mkComposite (dropEntry env vir) vi)

{- Everything that is in the parent Resouces but not in the child Resources of
   a SubRes is returned -}
keepEnv : Env ys -> (prf : SubRes xs ys) -> Env (kept prf)
keepEnv env SubNil = env
keepEnv env (InRes elRe rsr) = 
  let kep = keepEnv (dropDups env elRe) rsr
      kepPrf = keepEnvPrf elRe rsr env kep
  in rewrite__impl Env kepPrf kep
--keepEnv (dropDups env el) prf
keepEnv (z :: zs) (Skip prf) = z :: keepEnv zs prf

--rebldPrf : {sub,yres : Resources} -> ty -> Env yres -> (subRes: SubRes sub yres) -> (new_1 : Env new) -> Env (MkRes lbl ty :: updateWith new yres subRes) -> updateWith new (MkRes lbl ty :: yres) (Skip subRes) = (MkRes lbl ty :: updateWith new yres subRes)

-- Corresponds pretty much exactly to 'updateWith'
rebuildEnv : Env new -> Env old -> (prf : SubRes sub old) ->
             Env (updateWith new old prf)
rebuildEnv new [] SubNil = new
rebuildEnv new [] (InRes el p) = absurd el
rebuildEnv [] (x :: xs) (InRes el p)
    = rebuildEnv [] (dropDups (x :: xs) el) p
rebuildEnv (e :: es) (x :: xs) (InRes el p)
    = e :: rebuildEnv es (dropDups (x :: xs) el) p
rebuildEnv new (x :: xs) (Skip p) = 
   let res = x :: rebuildEnv new xs p
   in rewrite__impl Env rebldPrf res
   
runST : {invars : Resources} -> {m : Type -> Type} -> { a : Type } ->  {b : Type}->
        {outfn : a -> Resources} ->
        Env invars -> STrans m a invars outfn ->
        ((x : a) -> Env (outfn x) -> m b) -> m b
runST env (Pure result) k = k result env
--runST env (Bind x f) k = ?runST_rhs_2
runST env (Bind {a=bindedA} {st2_fn} prog next) k  --?xxx 
    = runST env prog (\prog', env' => runST env' (next prog') k) 
runST env (Lift action) k
   = do res <- action
        k res env
runST env (RunAs prog) k = runST env prog (\res, env' => k (pure res) env')
runST env (New val) k = k MkVar (val :: env)
runST env (Delete lbl prf) k = k () (dropVal prf env)
runST env (DropSubRes prf) k = k (dropEnv env prf) (keepEnv env prf)
runST env (Split lbl prf) k = let val = lookupEnv prf env
                                  env' = updateEnv prf env (Value ()) in
                                  k (mkVars val) (addToEnv val env')
  where
    mkVars : Composite ts -> VarList ts
    mkVars CompNil = []
    mkVars (CompCons x xs) = MkVar :: mkVars xs

    addToEnv : (comp : Composite ts) -> Env xs -> Env (mkRes (mkVars comp) ++ xs)
    addToEnv CompNil env = env
    addToEnv (CompCons x xs) env = x :: addToEnv xs env
runST env (Combine lbl vs prf) k = k () (rebuildVarsIn env prf)
runST env (ToEnd var prf) k = k () (dropVal prf env ++ [lookupEnv prf env])
runST env (Call prog res_prf) k
   = let env' = dropEnv env res_prf in
         runST env' prog
                 (\prog', envk => k prog' (rebuildEnv envk env res_prf))
runST env (Read lbl prf) k = k (lookupEnv prf env) env
runST env (Write lbl prf val) k = k () (updateEnv prf env val)

runSTLoop : {invars : Resources} -> {m : Type -> Type} -> {b : Type} -> Fuel -> Env invars -> STransLoop m a invars outfn ->
            (k : (x : a) -> Env (outfn x) -> m b) ->
            (onDry : m b) -> m b
runSTLoop Dry _ _ _ onDry = onDry
runSTLoop (More x) env (Bind prog next) k onDry
    = runST env prog (\prog', env' => runSTLoop x env' (next prog') k onDry)
runSTLoop (More x) env (Pure result) k onDry = k result env

export
pure : (result : ty) -> STrans m ty (out_fn result) out_fn
pure = Pure

export
(>>=) : {a : Type} -> {st2_fn : a -> Resources} -> STrans m a st1 st2_fn ->
        ((result : a) -> STrans m b (st2_fn result) st3_fn) ->
        STrans m b st1 st3_fn
(>>=) = Bind

export
returning : {out_fn : _ } -> (result : ty) -> STrans m () res (const (out_fn result)) ->
            STrans m ty res out_fn
returning res prog = do prog
                        pure res


export
lift : Monad m => m t -> STrans m t res (const res)
lift = Lift

export
runAs : {t : Type} -> {out_res : _} -> Applicative m => STrans m t in_res (const out_res) ->
        STrans m (m t) in_res (const out_res)
runAs = RunAs

export
new : (val : state) ->
      STrans m Var res (\lbl => (lbl ::: State state) :: res)
new val = New (Value val)

export
delete : (lbl : Var) ->
         {auto prf : InState lbl (State st) res} ->
         STrans m () res (const (drop res prf))
delete lbl {prf} = Delete lbl prf

-- Keep only a subset of the current set of resources. Returns the
-- environment corresponding to the dropped portion.
export
dropSub : {auto prf : SubRes ys xs} ->
          STrans m (Env ys) xs (const (kept prf))
dropSub {prf} = DropSubRes prf

export
split : (lbl : Var) ->
        {auto prf : InState lbl (Composite vars) res} ->
        STrans m (VarList vars) res
              (\vs => mkRes vs ++
                       updateRes res prf (State ()))
split lbl {prf} = Split lbl prf

export
combine : (comp : Var) -> (vs : List Var) ->
          {auto prf : InState comp (State ()) res} ->
          {auto var_prf : VarsIn (comp :: vs) res} ->
          STrans m () res
              (const (combineVarsIn res var_prf))
combine comp vs {var_prf} = Combine comp vs var_prf

export
toEnd : (lbl : Var) ->
        {auto prf : InState lbl state res} ->
        STrans m () res (const (drop res prf ++ [lbl ::: state]))
toEnd lbl {prf} = ToEnd lbl prf

export -- implicit ???
call : {sub,new_f : _ } -> STrans m t sub new_f ->
       {auto res_prf : SubRes sub old} ->
       STrans m t old (\res => updateWith (new_f res) old res_prf)
call prog {res_prf} = Call prog res_prf

export
read : {ty,res : _ } -> (lbl : Var) ->
       {auto prf : InState lbl (State ty) res} ->
       STrans m ty res (const res)
read lbl {prf} = do Value x <- Read lbl prf
                    pure x

export
write : (lbl : Var) ->
        {auto prf : InState lbl ty res} ->
        (val : ty') ->
        STrans m () res (const (updateRes res prf (State ty')))
write lbl {prf} val = Write lbl prf (Value val)

export
update : {ty,res : _ } -> (lbl : Var) ->
         {auto prf : InState lbl (State ty) res} ->
         (ty -> ty') ->
         STrans m () res (const (updateRes res prf (State ty')))
update lbl f = do x <- read lbl
                  write lbl (f x)

namespace Loop
   export
   (>>=) : {a : Type } -> {st2_fn : a -> Resources} -> STrans m a st1 st2_fn ->
          ((result : a) -> Inf (STransLoop m b (st2_fn result) st3_fn)) ->
          STransLoop m b st1 st3_fn
   (>>=) = Bind

   export
   pure : (result : ty) -> STransLoop m ty (out_fn result) out_fn
   pure = Pure

public export --%error_reduce
out_res : ty -> (as : List (Action ty)) -> Resources
out_res x [] = []
out_res x ((Stable lbl inr) :: xs) = (lbl ::: inr) :: out_res x xs
out_res x ((Trans lbl inr outr) :: xs)
    = (lbl ::: outr x) :: out_res x xs
out_res x ((Remove lbl inr) :: xs) = out_res x xs
out_res x (Add outf :: xs) = outf x ++ out_res x xs

public export --%error_reduce
in_res : (as : List (Action ty)) -> Resources
in_res [] = []
in_res ((Stable lbl inr) :: xs) = (lbl ::: inr) :: in_res xs
in_res ((Trans lbl inr outr) :: xs) = (lbl ::: inr) :: in_res xs
in_res ((Remove lbl inr) :: xs) = (lbl ::: inr) :: in_res xs
in_res (Add outf :: xs) = in_res xs

public export
--%error_reduce -- always evaluate this before showing errors
ST : (m : Type -> Type) ->
     (ty : Type) ->
     List (Action ty) -> Type
ST m ty xs = STrans m ty (in_res xs) (\result : ty => out_res result xs)

public export
--%error_reduce -- always evaluate this before showing errors
STLoop : (m : Type -> Type) ->
         (ty : Type) ->
         List (Action ty) -> Type
STLoop m ty xs = STransLoop m ty (in_res xs) (\result : ty => out_res result xs)

-- Console IO is useful sufficiently often that let's have it here
public export
interface ConsoleIO (m : Type -> Type) where
  putStr : String -> STrans m () xs (const xs)
  getStr : STrans m String xs (const xs)

  putChar : Char -> STrans m () xs (const xs)
  getChar : STrans m Char xs (const xs)


export
putStrLn : ConsoleIO m => String -> STrans m () xs (const xs)
putStrLn str = putStr (str ++ "\n")

export
print : (ConsoleIO m, Show a) => a -> STrans m () xs (const xs)
print a = putStr $ show a

export
printLn : (ConsoleIO m, Show a) => a -> STrans m () xs (const xs)
printLn a = putStrLn $ show a

export
ConsoleIO IO where
  putStr str = lift (putStr str)
  getStr = lift getLine

  putChar c = lift (putChar c)
  getChar = lift getChar

-- co: IOExcept doesn't exist in Idris2, not sure if there is an alternative
-- export
-- ConsoleIO (IOExcept err) where
--   putStr str = lift (ioe_lift (Interactive.putStr str))
--   getStr = lift (ioe_lift Interactive.getLine)

--   putChar c = lift (ioe_lift (Interactive.putChar c))
--   getChar = lift (ioe_lift Interactive.getChar)

export
run : {m,a : _ } -> Applicative m => ST m a [] -> m a
run prog = runST [] prog (\res, env' => pure res)

export
runLoop : {m,a : _} -> Applicative m => Fuel -> STLoop m a [] ->
          (onDry : m a) ->
          m a
runLoop fuel prog onDry
    = runSTLoop fuel [] prog (\res, env' => pure res) onDry

||| runWith allows running an STrans program with an initial environment,
||| which must be consumed.
||| It's only allowed in the IO monad, because it's inherently unsafe, so
||| we don't want to be able to use it under a 'lift' in just *any* ST program -
||| if we have access to an 'Env' we can easily duplicate it - so it's the
||| responsibility of an implementation of an interface in IO which uses it
||| to ensure that it isn't duplicated.
export
runWith : {res,a : _ } -> {resf : a -> Resources} -> Env res -> STrans IO a res resf ->
          IO (result ** Env (resf result))
runWith env prog = runST env prog (\res, env' => pure (res ** env'))

export
runWithLoop : {res,a : _ } -> {resf : a -> Resources} -> Env res -> Fuel -> STransLoop IO a res resf  ->
              IO (Maybe (result ** Env (resf result)))
runWithLoop env fuel prog
    = runSTLoop fuel env prog (\res, env' => pure (Just (res ** env')))
                              (pure Nothing)

export
runPure : {a : _ } -> ST Prelude.id a [] -> a
runPure prog = runST [] prog (\res, env' => res)

-- %language ErrorReflection

-- %error_handler
-- export
-- st_precondition : Err -> Maybe (List ErrorReportPart)
-- st_precondition (CantSolveGoal `(SubRes ~sub ~all) _)
--    = pure
--       [TextPart "'call' is not valid here. ",
--        TextPart "The operation has preconditions ",
--        TermPart sub,
--        TextPart " which is not a sub set of ",
--        TermPart all]
-- st_precondition (CantUnify _ tm1 tm2 _ _ _)
--    = do reqPre <- getPreconditions tm1
--         gotPre <- getPreconditions tm2
--         reqPost <- getPostconditions tm1
--         gotPost <- getPostconditions tm2
--         pure $ [TextPart "Error in state transition:"] ++
--                 renderPre gotPre reqPre ++
--                 renderPost gotPost reqPost

--   where
--     getPreconditions : TT -> Maybe TT
--     getPreconditions `(STrans ~m ~ret ~pre ~post) = Just pre
--     getPreconditions `(STransLoop ~m ~ret ~pre ~post) = Just pre
--     getPreconditions _ = Nothing

--     getPostconditions : TT -> Maybe TT
--     getPostconditions `(STrans ~m ~ret ~pre ~post) = Just post
--     getPostconditions `(STransLoop ~m ~ret ~pre ~post) = Just post
--     getPostconditions _ = Nothing

--     renderPre : TT -> TT -> List (ErrorReportPart)
--     renderPre got req
--         = [SubReport [TextPart "Operation has preconditions: ",
--                       TermPart req],
--            SubReport [TextPart "States here are: ",
--                       TermPart got]]
--     renderPost : TT -> TT -> List (ErrorReportPart)
--     renderPost got req
--         = [SubReport [TextPart "Operation has postconditions: ",
--                       TermPart req],
--            SubReport [TextPart "Required result states here are: ",
--                       TermPart got]]

-- st_precondition _ = Nothing
