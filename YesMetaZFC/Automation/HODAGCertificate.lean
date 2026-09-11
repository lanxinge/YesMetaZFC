import YesMetaZFC.Automation.HODAGCertificate.Core
import YesMetaZFC.Automation.GuardSemantics
namespace YesMetaZFC
namespace Automation
namespace HODAGCertificate
open Logic.HigherOrder
universe u v w x
section HODAGCertificateSignature
variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.BaseSort]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]
/-! ## 原生高阶整图证书 -/
structure Problem (σ : Signature.{u, v, w}) where
  initialClauses : Array (Clause σ)
namespace Problem
def Satisfies  {M : Structure.{u, v, w, x} σ} (problem : Problem σ) (env : Logic.HigherOrder.Env M) : Prop :=
  ∀ (index : Nat) (clause : Clause σ),
    problem.initialClauses[index]? = some clause → clause.Satisfies env
def Valid  (M : Structure.{u, v, w, x} σ) (problem : Problem σ) : Prop :=
  ∀ env : Logic.HigherOrder.Env M, env.WellSorted [] → problem.Satisfies env
end Problem
/-! ## Residual CDCL 证书 -/
structure PropLiteralLink (σ : Signature.{u, v, w}) where
  prop : PropResolution.Lit
  object : Literal σ
namespace PropLiteralLink
def valuation  {M : Structure.{u, v, w, x} σ} (base : PropResolution.Valuation) (atomMap : Array (Atom σ))
    (env : Logic.HigherOrder.Env M) : PropResolution.Valuation :=
  fun var =>
    match atomMap[var]? with
    | some atom => atom.Satisfies env
    | none => base var
def outsideAtomMap  (atomMap : Array (Atom σ)) (lit : PropResolution.Lit) : Bool :=
  match atomMap[lit.var]? with
  | some _ => false
  | none => true
def check (atomMap : Array (Atom σ)) (link : PropLiteralLink σ) : Bool :=
  link.prop.positive == link.object.polarity &&
    match atomMap[link.prop.var]? with
    | some atom => atom.eq link.object.atom
    | none => false
theorem sound
    {M : Structure.{u, v, w, x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Atom σ)} {env : Logic.HigherOrder.Env M}
    {link : PropLiteralLink σ} (hCheck : link.check atomMap = true) (hObject : link.object.Satisfies env) :
    link.prop.Holds (valuation base atomMap env) := by
  cases link with
  | mk prop object =>
    cases prop with
    | mk var positive =>
      cases object with
      | mk objectPolarity objectAtom =>
        unfold check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hPolarity, hAtomCheck⟩
        have hPolarityEq : positive = objectPolarity :=
          beq_iff_eq.mp hPolarity
        cases hLookup : atomMap[var]? with
        | none =>
            simp [hLookup] at hAtomCheck
        | some atom =>
            have hAtomEq : atom = objectAtom :=
              Atom.eq_sound atom objectAtom (by simpa [hLookup] using hAtomCheck)
            cases hPolarityEq
            cases positive <;>
              simpa [PropResolution.Lit.Holds, valuation, Literal.Satisfies,
                hLookup, hAtomEq] using hObject
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem holds_valuation_iff_of_outsideAtomMap
     {M : Structure.{u, v, w, x} σ}
    {base : PropResolution.Valuation} {atomMap : Array (Atom σ)}
    {env : Logic.HigherOrder.Env M} {lit : PropResolution.Lit} (hOutside : outsideAtomMap atomMap lit = true) :
    lit.Holds (valuation base atomMap env) ↔ lit.Holds base := by
  cases lit with
  | mk var positive =>
      unfold outsideAtomMap at hOutside
      cases hLookup : atomMap[var]? with
      | some atom =>
          simp [hLookup] at hOutside
      | none =>
          cases positive <;>
            simp [PropResolution.Lit.Holds, valuation, hLookup]
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem outsideAtomMap_neg
    {atomMap : Array (Atom σ)} {lit : PropResolution.Lit} (hOutside : outsideAtomMap atomMap lit = true) :
    outsideAtomMap atomMap lit.neg = true := by
  cases lit
  simpa [outsideAtomMap, PropResolution.Lit.neg] using hOutside
end PropLiteralLink
structure PropParentClauseLink (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  literalLinks : Array (PropLiteralLink σ)
namespace PropParentClauseLink
def encodedClause  (link : PropParentClauseLink σ) :
    PropResolution.Clause :=
  PropResolution.canonicalClause (link.literalLinks.map fun literal => literal.prop)
def objectClause  (link : PropParentClauseLink σ) :
    Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }
def check (parents : Array Nat) (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause) (link : PropParentClauseLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.literalLinks.all fun literal => literal.check atomMap
theorem encodedClause_satisfies_of_object
    {M : Structure.{u, v, w, x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Atom σ)} {env : Logic.HigherOrder.Env M}
    {link : PropParentClauseLink σ} (hLiteralChecks : (link.literalLinks.all fun literal => literal.check atomMap) = true)
    (hObject : link.objectClause.Satisfies env) :
    PropResolution.Clause.Satisfies (PropLiteralLink.valuation base atomMap env) link.encodedClause := by
  rcases hObject with ⟨objectLiteral, hObjectMem, hObjectSat⟩
  rcases Array.mem_map.mp hObjectMem with ⟨item, hItem, rfl⟩
  apply PropResolution.Clause.satisfies_canonical_iff.mpr
  exact ⟨item.prop, Array.mem_def.mp (Array.mem_map_of_mem hItem),
    PropLiteralLink.sound (Array.all_eq_true'.mp hLiteralChecks item hItem) hObjectSat⟩

end PropParentClauseLink
structure PropGuardActivationLink (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  guards : GuardSet
  literalLinks : Array (PropLiteralLink σ)
namespace PropGuardActivationLink
def encodedClause  (link : PropGuardActivationLink σ) :
    PropResolution.Clause :=
  PropResolution.canonicalClause (link.guards.map PropResolution.Lit.neg ++
      link.literalLinks.map fun literal => literal.prop)
def objectClause  (link : PropGuardActivationLink σ) :
    Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }
def check (parents : Array Nat) (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause) (link : PropGuardActivationLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.guards.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
          link.literalLinks.all fun literal => literal.check atomMap
theorem encodedClause_satisfies
    {M : Structure.{u, v, w, x} σ} {base : PropResolution.Valuation}
    {atomMap : Array (Atom σ)} {env : Logic.HigherOrder.Env M}
    {link : PropGuardActivationLink σ} (hGuardChecks : (link.guards.all fun literal =>
        PropLiteralLink.outsideAtomMap atomMap literal) = true) (hLiteralChecks : (link.literalLinks.all fun literal => literal.check atomMap) = true)
    (hObjectOfGuards : (∀ lit, lit ∈ (Guards.canonical link.guards).toList → lit.Holds base) →
        link.objectClause.Satisfies env) :
    PropResolution.Clause.Satisfies (PropLiteralLink.valuation base atomMap env) link.encodedClause := by
  apply Guards.activation_satisfies
  · intro lit hMem
    exact PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
      (Array.all_eq_true'.mp hGuardChecks lit (Array.mem_def.mpr hMem))
  · intro hGuards
    exact PropResolution.Clause.satisfies_canonical_iff.mp
      (PropParentClauseLink.encodedClause_satisfies_of_object
        (link := ⟨link.parent, link.literalLinks⟩) hLiteralChecks
        (hObjectOfGuards hGuards))

end PropGuardActivationLink
structure PropLearnedClauseLink where
  parent : Nat
  guards : GuardSet
  clause : PropResolution.Clause
namespace PropLearnedClauseLink
def check  (parents : Array Nat) (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause) (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    link.clause.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq link.clause (Guards.learnedClause link.guards) &&
        PropResolution.clauseEq initial.clause link.clause
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_of_not_guards
     {M : Structure.{u, v, w, x} σ}
    {base : PropResolution.Valuation} {atomMap : Array (Atom σ)}
    {env : Logic.HigherOrder.Env M} {link : PropLearnedClauseLink}
    {guards : GuardSet} (hClause : link.clause = Guards.learnedClause guards) (hOutside : (link.clause.all fun literal =>
        PropLiteralLink.outsideAtomMap atomMap literal) = true) (hNotGuards :
      ¬ ∀ lit, lit ∈ (Guards.canonical guards).toList → lit.Holds base) :
    PropResolution.Clause.Satisfies (PropLiteralLink.valuation base atomMap env) link.clause := by
  have hSat : PropResolution.Clause.Satisfies base link.clause := by
    rw [hClause]
    exact Guards.learnedClause_satisfies_iff.mpr hNotGuards
  exact hSat.transfer fun lit hMem hHolds =>
    (PropLiteralLink.holds_valuation_iff_of_outsideAtomMap
      (Array.all_eq_true'.mp hOutside lit (Array.mem_def.mpr hMem))).mpr hHolds

end PropLearnedClauseLink
structure PropAvatarSkeletonLink where
  parent : Nat
  skeleton : PropResolution.Clause
namespace PropAvatarSkeletonLink
def check  (parents : Array Nat) (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause) (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    link.skeleton.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq initial.clause link.skeleton
end PropAvatarSkeletonLink
inductive PropInitialJustification (σ : Signature.{u, v, w}) where
  | parentClause (link : PropParentClauseLink σ)
  | guardActivationClause (link : PropGuardActivationLink σ)
  | propLearnedClause (link : PropLearnedClauseLink)
  | avatarSkeleton (link : PropAvatarSkeletonLink)
namespace PropInitialJustification
def parentClause? :
    PropInitialJustification σ → Option (ParentClause σ)
  | .parentClause link => some link.parent
  | .guardActivationClause link => some link.parent
  | .propLearnedClause _ | .avatarSkeleton _ => none
def check (parents : Array Nat) (atomMap : Array (Atom σ)) (initial : PropResolution.InitialClause) : PropInitialJustification σ → Bool
  | .parentClause link => link.check parents atomMap initial
  | .guardActivationClause link => link.check parents atomMap initial
  | .propLearnedClause link => link.check parents atomMap initial
  | .avatarSkeleton link => link.check parents atomMap initial
def guardedSoundnessSupported :
    PropInitialJustification σ → Bool
  | .parentClause _ | .guardActivationClause _ | .propLearnedClause _ => true
  | .avatarSkeleton _ => false
end PropInitialJustification
structure PropositionalClosurePayload (σ : Signature.{u, v, w}) where
  atomMap : Array (Atom σ) := #[]
  initialClauses : Array PropResolution.InitialClause
  initialJustifications : Array (PropInitialJustification σ)
  proof : PropResolution.CdclProof
namespace PropositionalClosurePayload
def parentClauses (payload : PropositionalClosurePayload σ) : Array (ParentClause σ) :=
  payload.initialJustifications.filterMap PropInitialJustification.parentClause?
def justificationsCheck (parents : Array Nat) (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialClauses.size == payload.initialJustifications.size && (payload.initialClauses.mapIdx fun index initial =>
      match payload.initialJustifications[index]? with
      | some justification => justification.check parents payload.atomMap initial
      | none => false).all fun ok => ok
def guardedSoundnessSupported (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all PropInitialJustification.guardedSoundnessSupported
def check (parents : Array Nat) (payload : PropositionalClosurePayload σ) : Bool :=
  PropResolution.checkedUnsat payload.initialClauses payload.proof &&
    payload.justificationsCheck parents
def ofCheckedUnsat (cert : PropResolution.CheckedUnsatCertificate) (atomMap : Array (Atom σ)) (initialJustifications : Array (PropInitialJustification σ)) :
    PropositionalClosurePayload σ := {
  atomMap := atomMap
  initialClauses := cert.initialClauses
  initialJustifications := initialJustifications
  proof := cert.proof
}
end PropositionalClosurePayload
structure AvatarSplitPayload (σ : Signature.{u, v, w}) where
  source : ParentClause σ
  partitions : Array (Array Nat)
  selectors : PropResolution.Clause
namespace AvatarSplitPayload
def parentClauses  (payload : AvatarSplitPayload σ) :
    Array (ParentClause σ) :=
  #[payload.source]
def componentClauses  (payload : AvatarSplitPayload σ) :
    List (Clause σ) :=
  payload.partitions.toList.map (Avatar.clauseAtIndices payload.source.clause)
def check (parents : Array Nat) (payload : AvatarSplitPayload σ) : Bool :=
  parents.size == 1 &&
    payload.source.idIn parents &&
      payload.source.clause.check &&
        Automation.AvatarSplit.indexPartitionOk payload.source.clause.literals.size
          payload.partitions &&
          Automation.AvatarSplit.selectorsOk payload.partitions payload.selectors &&
            Avatar.pairwiseSupportDisjoint payload.componentClauses &&
              Clause.coversCheck payload.source.clause payload.componentClauses
end AvatarSplitPayload
structure AvatarComponentPayload (σ : Signature.{u, v, w}) where
  split : ParentClause σ
  componentIndex : Nat
  component : Clause σ
  selector : GuardLit
namespace AvatarComponentPayload
def parentClauses (payload : AvatarComponentPayload σ) : Array (ParentClause σ) :=
  #[payload.split]
def check (parents : Array Nat) (payload : AvatarComponentPayload σ) : Bool :=
  parents.size == 1 &&
    payload.split.idIn parents &&
      payload.component.check &&
        payload.selector.positive
end AvatarComponentPayload
structure AvatarSelectorComponent (σ : Signature.{u, v, w}) where
  selector : GuardLit
  component : Clause σ
namespace AvatarSelectorComponent
def ofLists :
    List GuardLit → List (Clause σ) → List (AvatarSelectorComponent σ)
  | selector :: selectors, component :: components =>
      ⟨selector, component⟩ :: ofLists selectors components
  | _, _ => []
def compatibleCheck (entries : List (AvatarSelectorComponent σ)) : Bool :=
  entries.all fun left =>
    entries.all fun right =>
      if left.selector.var == right.selector.var then
        left.component.eq right.component
      else
        true
end AvatarSelectorComponent
namespace AvatarSplitPayload
def selectorComponents (payload : AvatarSplitPayload σ) : List (AvatarSelectorComponent σ) :=
  AvatarSelectorComponent.ofLists payload.selectors.toList payload.componentClauses
end AvatarSplitPayload
structure TheoryConflictPayload (σ : Signature.{u, v, w}) where
  conflict : ParentClause σ
namespace TheoryConflictPayload
def parentClauses  (payload : TheoryConflictPayload σ) :
    Array (ParentClause σ) :=
  #[payload.conflict]
def check  (parents : Array Nat) (payload : TheoryConflictPayload σ) : Bool :=
  payload.conflict.idIn parents && payload.conflict.clause.isEmpty
end TheoryConflictPayload
structure PropositionalLearnedClausePayload where
  conflict : Nat
  learned : PropResolution.Clause
namespace PropositionalLearnedClausePayload
def check (parents : Array Nat) (payload : PropositionalLearnedClausePayload) : Bool :=
  parents.contains payload.conflict
end PropositionalLearnedClausePayload
/--
原生高阶整图 payload。
source、β、η 直接计算公理结论；substitution、standardize-apart 与局部高阶规则
从已检查父快照机械计算结论。
-/
inductive Payload (σ : Signature.{u, v, w}) where
  | source (initialIndex : Nat)
  | avatarSplit (payload : AvatarSplitPayload σ)
  | avatarComponent (payload : AvatarComponentPayload σ)
  | betaEta (payload : BetaEta.Payload σ)
  | substitution (evidence : Substitution.Evidence σ)
  | standardizeApart (evidence : StandardizeApart.Evidence σ)
  | resolution (evidence : Resolution.Evidence σ)
  | factoring (evidence : Factoring.Evidence σ)
  | equalityResolution (evidence : EqualityResolution.Evidence σ)
  | booleanExtensionality (evidence : BooleanExtensionality.Evidence σ)
  | rewrite (kind : RewriteKind) (evidence : Rewrite.Evidence σ)
  | argumentCongruence (evidence : ArgumentCongruence.Evidence σ)
  | functionExtensionality (evidence : FunctionExtensionality.Evidence σ)
  | theoryConflict (payload : TheoryConflictPayload σ)
  | propositionalLearnedClause (payload : PropositionalLearnedClausePayload)
  | residualCdcl (payload : PropositionalClosurePayload σ)
namespace Payload
def conclusion? (problem : Problem σ) :
    Payload σ → Option (Clause σ)
  | .source initialIndex => problem.initialClauses[initialIndex]?
  | .avatarSplit payload => some payload.source.clause
  | .avatarComponent payload => some payload.component
  | .betaEta payload => some payload.conclusion
  | .substitution evidence => some evidence.conclusion
  | .standardizeApart evidence => some evidence.conclusion
  | .resolution evidence => some evidence.conclusion
  | .factoring evidence => some evidence.conclusion
  | .equalityResolution evidence => some evidence.conclusion
  | .booleanExtensionality evidence => some evidence.conclusion
  | .rewrite _ evidence => some evidence.conclusion
  | .argumentCongruence evidence => some evidence.conclusion
  | .functionExtensionality evidence => some evidence.conclusion
  | .theoryConflict _ => some { literals := #[] }
  | .propositionalLearnedClause _ => some { literals := #[] }
  | .residualCdcl _ => some { literals := #[] }
def parentClauses : Payload σ → Array (ParentClause σ)
  | .substitution evidence => #[evidence.parent]
  | .avatarSplit payload => payload.parentClauses
  | .avatarComponent payload => payload.parentClauses
  | .standardizeApart evidence => #[evidence.parent]
  | .resolution evidence => #[evidence.left, evidence.right]
  | .factoring evidence => #[evidence.parent]
  | .equalityResolution evidence => #[evidence.parent]
  | .booleanExtensionality evidence => #[evidence.parent]
  | .rewrite _ evidence => #[evidence.equality, evidence.target]
  | .argumentCongruence evidence => #[evidence.parent]
  | .functionExtensionality evidence => #[evidence.parent]
  | .theoryConflict payload => payload.parentClauses
  | .residualCdcl payload => payload.parentClauses
  | _ => #[]
def soundnessSupportedWithWitness  (hasWitness : Bool) : Payload σ → Bool
  | .avatarSplit _ => false
  | .avatarComponent _ => false
  | .functionExtensionality _ => hasWitness
  | .theoryConflict _ => false
  | .propositionalLearnedClause _ => false
  | .residualCdcl _ => false
  | _ => true
def soundnessSupported  (payload : Payload σ) : Bool :=
  payload.soundnessSupportedWithWitness true
/--
payload checker。
source、β、η 是零父边公理节点；其余节点检查父边引用、规则专用 witness 与机械结果。
-/
def ruleCheck (problem : Problem σ) (parents : Array Nat) : Payload σ → Bool
  | .source initialIndex =>
      parents.isEmpty &&
        match problem.initialClauses[initialIndex]? with
        | some clause => clause.check
        | none => false
  | .avatarSplit payload => payload.check parents
  | .avatarComponent payload => payload.check parents
  | .betaEta payload => parents.isEmpty && payload.check
  | .substitution evidence => evidence.check parents
  | .standardizeApart evidence => evidence.check parents
  | .resolution evidence => evidence.check parents
  | .factoring evidence => evidence.check parents
  | .equalityResolution evidence => evidence.check parents
  | .booleanExtensionality evidence => evidence.check parents
  | .rewrite kind evidence => evidence.check kind parents
  | .argumentCongruence evidence => evidence.check parents
  | .functionExtensionality evidence => evidence.check parents
  | .theoryConflict payload => payload.check parents
  | .propositionalLearnedClause payload => payload.check parents
  | .residualCdcl payload => !parents.isEmpty && payload.check parents
def parentIdsCheck (payload : Payload σ) (parents : Array Nat) : Bool :=
  payload.parentClauses.all fun parent => parent.idIn parents
def check (problem : Problem σ) (parents : Array Nat) (payload : Payload σ) : Bool :=
  payload.parentIdsCheck parents && payload.ruleCheck problem parents
theorem ruleCheck_of_check
    {problem : Problem σ} {parents : Array Nat} {payload : Payload σ} (hCheck : payload.check problem parents = true) :
    payload.ruleCheck problem parents = true := (Bool.and_eq_true_iff.mp hCheck).2
theorem parentIdsIn_of_check
    {problem : Problem σ} {parents : Array Nat} {payload : Payload σ} (hCheck : payload.check problem parents = true) :
    ∀ parent, parent ∈ payload.parentClauses.toList → parent.id ∈ parents.toList := by
  intro parent hParent
  exact ParentClause.mem_toList_of_idIn
    (Array.all_eq_true'.mp (Bool.and_eq_true_iff.mp hCheck).1 parent
      (Array.mem_def.mpr hParent))

theorem conclusion_exists_of_check
    {problem : Problem σ} {parents : Array Nat} {payload : Payload σ} (hCheck : payload.check problem parents = true) :
    ∃ conclusion, payload.conclusion? problem = some conclusion := by
  have hRuleCheck := ruleCheck_of_check hCheck
  cases payload with
  | source initialIndex =>
      cases hConclusion : problem.initialClauses[initialIndex]? with
      | none =>
          simp [ruleCheck, hConclusion] at hRuleCheck
      | some conclusion =>
          exact ⟨conclusion, by simp [conclusion?, hConclusion]⟩
  | avatarSplit payload =>
      exact ⟨payload.source.clause, by simp [conclusion?]⟩
  | avatarComponent payload =>
      exact ⟨payload.component, by simp [conclusion?]⟩
  | betaEta payload => exact ⟨payload.conclusion, by simp [conclusion?]⟩
  | substitution evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | standardizeApart evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | resolution evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | factoring evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | equalityResolution evidence => exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | booleanExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | rewrite kind evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | argumentCongruence evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | functionExtensionality evidence =>
      exact ⟨evidence.conclusion, by simp [conclusion?]⟩
  | theoryConflict payload => exact ⟨{ literals := #[] }, by simp [conclusion?]⟩
  | propositionalLearnedClause payload =>
      exact ⟨{ literals := #[] }, by simp [conclusion?]⟩
  | residualCdcl payload => exact ⟨{ literals := #[] }, by simp [conclusion?]⟩
end Payload
structure Node (σ : Signature.{u, v, w}) where
  id : Nat
  parents : Array Nat
  guards : GuardSet := #[]
  payload : Payload σ
namespace Node
def conclusion? (problem : Problem σ) (node : Node σ) : Option (Clause σ) :=
  node.payload.conclusion? problem
def guardedConclusion (problem : Problem σ) (node : Node σ) : Option (GuardedClause σ) := do
  let conclusion ← node.conclusion? problem
  some { guards := node.guards, clause := conclusion }
def unguarded  (node : Node σ) : Bool :=
  node.guards.isEmpty
def globallyClosed (problem : Problem σ) (node : Node σ) : Bool :=
  match node.conclusion? problem with
  | some conclusion => node.unguarded && conclusion.isEmpty
  | none => false
def theoryConflict (problem : Problem σ) (node : Node σ) : Bool :=
  match node.conclusion? problem with
  | some conclusion => !node.unguarded && conclusion.isEmpty
  | none => false
def check (problem : Problem σ) (node : Node σ) : Bool :=
  node.payload.check problem node.parents
def GuardsHold (valuation : PropResolution.Valuation) (guards : GuardSet) : Prop :=
  ∀ lit, lit ∈ (Guards.canonical guards).toList → lit.Holds valuation
theorem GuardsHold.of_guardSetEq {valuation : PropResolution.Valuation}
    {left right : GuardSet} (hEq : Guards.eq left right = true) (hGuards : GuardsHold valuation left) :
    GuardsHold valuation right := by
  intro lit hLit
  have hCanonical : Guards.canonical left = Guards.canonical right :=
    PropResolution.clauseEq_eq.mp (by simpa [Guards.eq] using hEq)
  exact hGuards lit (by simpa [hCanonical] using hLit)
theorem GuardsHold.empty (valuation : PropResolution.Valuation) :
    GuardsHold valuation (#[] : GuardSet) := by
  intro lit hLit
  have hRaw : lit ∈ (#[] : GuardSet).toList :=
    Guards.mem_of_mem_canonical hLit
  simp at hRaw
theorem GuardsHold.of_isEmpty {valuation : PropResolution.Valuation}
    {guards : GuardSet} (hEmpty : guards.isEmpty = true) :
    GuardsHold valuation guards := by
  have hGuards : guards = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    have hBool : (guards.size == 0) = true := by
      simpa [Array.isEmpty] using hEmpty
    exact beq_iff_eq.mp hBool
  subst guards
  exact GuardsHold.empty valuation
end Node
structure DAG (σ : Signature.{u, v, w}) where
  problem : Problem σ
  root : Nat
  nodes : Array (Node σ)
namespace DAG
def graphView (dag : DAG σ) : DenseDAG.View (Node σ) where
  nodes := dag.nodes
  root := dag.root
  node_id := Node.id
  node_parents := Node.parents
def node?  (dag : DAG σ) (id : Nat) : Option (Node σ) :=
  dag.graphView.node? id
def nodeAt  (dag : DAG σ) (index : Nat) (hIndex : index < dag.nodes.size) : Node σ :=
  dag.graphView.nodeAt index hIndex
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
@[simp]
theorem node?_eq_some_nodeAt  (dag : DAG σ) {index : Nat} (hIndex : index < dag.nodes.size) :
    dag.node? index = some (dag.nodeAt index hIndex) := by
  simpa [node?, nodeAt, graphView] using
    DenseDAG.View.node?_eq_some_nodeAt dag.graphView hIndex
def parentSnapshotChecked (dag : DAG σ) (parent : ParentClause σ) : Bool :=
  match dag.node? parent.id with
  | some node =>
      match node.conclusion? dag.problem with
      | some conclusion => parent.clause.eq conclusion
      | none => false
  | none => false
theorem parentSnapshotChecked_sound
    {dag : DAG σ} {parent : ParentClause σ} (hChecked : dag.parentSnapshotChecked parent = true) :
    ∃ node conclusion,
      dag.node? parent.id = some node ∧
        node.conclusion? dag.problem = some conclusion ∧
          parent.clause = conclusion := by
  unfold parentSnapshotChecked at hChecked
  cases hNode : dag.node? parent.id with
  | none =>
      simp [hNode] at hChecked
  | some node =>
      cases hConclusion : node.conclusion? dag.problem with
      | none =>
          simp [hNode, hConclusion] at hChecked
      | some conclusion =>
          have hClause : parent.clause.eq conclusion = true := by
            simpa [hNode, hConclusion] using hChecked
          exact ⟨node, conclusion, rfl, hConclusion,
            Clause.eq_sound parent.clause conclusion hClause⟩
def parentSnapshotsChecked (dag : DAG σ) : Bool :=
  dag.nodes.all fun node =>
    node.payload.parentClauses.all fun parent => dag.parentSnapshotChecked parent
theorem parentSnapshotChecked_of_eq_true
    {dag : DAG σ} (hSnapshots : dag.parentSnapshotsChecked = true) (index : Nat) (hIndex : index < dag.nodes.size) (parent : ParentClause σ)
    (hParent : parent ∈ (dag.nodeAt index hIndex).payload.parentClauses.toList) :
    dag.parentSnapshotChecked parent = true := by
  have hNodes := Array.all_eq_true.mp hSnapshots
  have hNode : ((dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        dag.parentSnapshotChecked parent) = true := by
    simpa [parentSnapshotsChecked, nodeAt] using! hNodes index hIndex
  have hParents := Array.all_eq_true.mp hNode
  have hArray : parent ∈ (dag.nodeAt index hIndex).payload.parentClauses :=
    Array.mem_def.mpr hParent
  rcases Array.mem_iff_getElem.mp hArray with ⟨parentIndex, hParentIndex, hGet⟩
  have hAt := hParents parentIndex hParentIndex
  simpa [hGet] using hAt
def parentGuards?  (dag : DAG σ) (id : Nat) : Option GuardSet := (dag.node? id).map Node.guards
def parentGuardUnionList?  (dag : DAG σ) :
    List Nat → Option GuardSet :=
  Guards.mergeList? dag.parentGuards?
def parentGuardUnion?  (dag : DAG σ) (parents : Array Nat) : Option GuardSet :=
  dag.parentGuardUnionList? parents.toList
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem mem_parentGuardUnionList_of_parent_mem
     {dag : DAG σ}
    {parents : List Nat} {parent : Nat} {parentNode : Node σ}
    {guards : GuardSet} {lit : GuardLit} (hUnion : dag.parentGuardUnionList? parents = some guards) (hParentMem : parent ∈ parents)
    (hParentNode : dag.node? parent = some parentNode) (hLit : lit ∈ (Guards.canonical parentNode.guards).toList) :
    lit ∈ (Guards.canonical guards).toList := by
  apply Guards.mem_canonical_mergeList_of_mem hUnion hParentMem ?_ hLit
  simp [parentGuards?, hParentNode]
def propParentInitialLinkOk (dag : DAG σ) (parents : Array Nat) (link : PropParentClauseLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
      match dag.node? link.parent.id with
      | some parentNode => parentNode.unguarded
      | none => false
def propGuardActivationInitialLinkOk (dag : DAG σ) (parents : Array Nat) (link : PropGuardActivationLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
      match dag.node? link.parent.id with
      | some parentNode =>
          !parentNode.unguarded && Guards.eq link.guards parentNode.guards
      | none => false
def propLearnedInitialLinkOk  (dag : DAG σ) (parents : Array Nat) (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        match parentNode.payload with
        | .propositionalLearnedClause payload =>
            Guards.eq link.guards parentNode.guards &&
              PropResolution.clauseEq link.clause payload.learned
        | _ => false
    | none => false
def propAvatarSkeletonInitialLinkOk (dag : DAG σ) (parents : Array Nat) (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        parentNode.unguarded &&
          match parentNode.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq link.skeleton (PropResolution.canonicalClause payload.selectors)
          | _ => false
    | none => false
def propInitialJustificationDagOk (dag : DAG σ) (parents : Array Nat) :
    PropInitialJustification σ → Bool
  | .parentClause link => dag.propParentInitialLinkOk parents link
  | .guardActivationClause link => dag.propGuardActivationInitialLinkOk parents link
  | .propLearnedClause link => dag.propLearnedInitialLinkOk parents link
  | .avatarSkeleton link => dag.propAvatarSkeletonInitialLinkOk parents link
def propInitialLinksOk (dag : DAG σ) (node : Node σ) : Bool :=
  match node.payload with
  | .residualCdcl payload =>
      payload.initialJustifications.all fun justification =>
        dag.propInitialJustificationDagOk node.parents justification
  | _ => true
def avatarSelectorComponents :
    Payload σ → List (AvatarSelectorComponent σ)
  | .avatarSplit payload =>
      payload.selectorComponents
  | _ => []
def avatarSelectorRegistry  (dag : DAG σ) :
    List (AvatarSelectorComponent σ) :=
  dag.nodes.toList.flatMap fun node => avatarSelectorComponents node.payload
def avatarSelectorRegistryChecked (dag : DAG σ) : Bool :=
  AvatarSelectorComponent.compatibleCheck dag.avatarSelectorRegistry
def payloadMergesParentGuards : Payload σ → Bool
  | .substitution _ | .standardizeApart _ | .resolution _ | .factoring _
  | .equalityResolution _ | .booleanExtensionality _ | .rewrite _ _
  | .argumentCongruence _
  | .functionExtensionality _ | .theoryConflict _ => true
  | _ => false
def payloadIsTheoryConflict : Payload σ → Bool
  | .theoryConflict _ => true
  | _ => false
def avatarSplitNodeOk (dag : DAG σ) (node : Node σ) (payload : AvatarSplitPayload σ) : Bool :=
  node.unguarded &&
    dag.parentSnapshotChecked payload.source &&
      match dag.node? payload.source.id with
      | some sourceNode =>
          sourceNode.unguarded &&
            match sourceNode.payload with
            | .source _ => true
            | _ => false
      | none => false
def avatarComponentNodeOk (dag : DAG σ) (node : Node σ) (payload : AvatarComponentPayload σ) : Bool :=
  dag.parentSnapshotChecked payload.split &&
    match dag.node? payload.split.id with
    | some splitNode =>
        splitNode.unguarded &&
          match splitNode.payload with
          | .avatarSplit splitPayload =>
              match splitPayload.partitions[payload.componentIndex]?,
                  Automation.AvatarSplit.selectorAt? splitPayload.selectors
                    payload.componentIndex with
              | some indices, some selector =>
                  payload.component.eq (Avatar.clauseAtIndices splitPayload.source.clause indices) &&
                    payload.selector == selector &&
                      Guards.eq node.guards #[selector]
              | _, _ => false
          | _ => false
    | none => false
def localNodeGuardsOk (dag : DAG σ) (node : Node σ) : Bool :=
  if payloadMergesParentGuards node.payload then
    match dag.parentGuardUnion? node.parents with
    | some guards => Guards.eq node.guards guards
    | none => false
  else
    match node.payload with
    | .avatarSplit payload =>
        dag.avatarSplitNodeOk node payload
    | .avatarComponent payload =>
        dag.avatarComponentNodeOk node payload
    | .propositionalLearnedClause payload =>
        match dag.node? payload.conflict with
        | some conflictNode =>
            payloadIsTheoryConflict conflictNode.payload &&
              conflictNode.theoryConflict dag.problem &&
                Guards.eq node.guards conflictNode.guards &&
                  PropResolution.clauseEq payload.learned (Guards.learnedClause conflictNode.guards)
        | none => false
    | .residualCdcl _ => node.unguarded
    | _ => true
def guardsChecked (dag : DAG σ) : Bool :=
  dag.nodes.all fun node =>
    dag.localNodeGuardsOk node && dag.propInitialLinksOk node
theorem guardsChecked_of_eq_true
     {dag : DAG σ} (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  have hAt := (Array.all_eq_true.mp hGuards) index hIndex
  exact (Bool.and_eq_true_iff.mp (by
    simpa [guardsChecked, nodeAt] using! hAt)).1
theorem propInitialLinksChecked_of_eq_true
     {dag : DAG σ} (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  have hAt := (Array.all_eq_true.mp hGuards) index hIndex
  exact (Bool.and_eq_true_iff.mp (by
    simpa [guardsChecked, nodeAt] using! hAt)).2
def rootExists  (dag : DAG σ) : Bool :=
  dag.graphView.rootExists
def rootClosed (dag : DAG σ) : Bool :=
  match dag.node? dag.root with
  | some node => node.globallyClosed dag.problem
  | none => false
def denseIds  (dag : DAG σ) : Bool :=
  dag.graphView.denseIds
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem denseIds_of_eq_true  {dag : DAG σ} (hDense : dag.denseIds = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).id = index := by
  simpa [denseIds, graphView, nodeAt] using
    DenseDAG.View.denseIds_of_eq_true (view := dag.graphView) hDense
def parentsBefore  (dag : DAG σ) : Bool :=
  dag.graphView.parentsBefore
def ParentsBefore  (dag : DAG σ) : Prop :=
  dag.graphView.ParentsBefore
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem parentsBefore_of_eq_true  {dag : DAG σ} (hParents : dag.parentsBefore = true) : dag.ParentsBefore := by
  simpa [parentsBefore, ParentsBefore, graphView, nodeAt] using
    DenseDAG.View.parentsBefore_of_eq_true (view := dag.graphView) hParents
def payloadsChecked (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.check dag.problem
theorem payloadsChecked_of_eq_true
    {dag : DAG σ} (hPayloads : dag.payloadsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).check dag.problem = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hPayloads
  simpa [payloadsChecked, nodeAt] using! hAll index hIndex
structure NodeContract (dag : DAG σ) (index : Nat) (hIndex : index < dag.nodes.size) : Prop where
  node_id : (dag.nodeAt index hIndex).id = index
  node_checked : (dag.nodeAt index hIndex).check dag.problem = true
  guards_checked : dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true
  prop_initial_links_checked :
    dag.propInitialLinksOk (dag.nodeAt index hIndex) = true
/--
整张高阶 DAG 的结构契约。
checker 的根、拓扑与节点信息在 checked 证书构造时统一提取；soundness 层只消费
该契约，不再重复展开同一个整图布尔等式。
-/
structure Contract (dag : DAG σ) : Prop where
  root_exists : dag.root < dag.nodes.size
  root_closed : dag.rootClosed = true
  root_conclusion :
    ∃ conclusion, (dag.nodeAt dag.root root_exists).conclusion? dag.problem = some conclusion ∧
        conclusion.isEmpty = true
  root_unguarded : (dag.nodeAt dag.root root_exists).unguarded = true
  dense_ids : dag.denseIds = true
  parents_before : dag.ParentsBefore
  payloads_checked : dag.payloadsChecked = true
  parent_snapshots_checked : dag.parentSnapshotsChecked = true
  guards_checked : dag.guardsChecked = true
  node_contract :
    ∀ index (hIndex : index < dag.nodes.size), NodeContract dag index hIndex
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
/--
拓扑归纳骨架。
节点性质只依赖父节点性质时，`ParentsBefore` 允许按 dense 数组顺序推广到整张图。
-/
theorem topologicalInduction (dag : DAG σ) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < dag.nodes.size), (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex) (dag.nodeAt parent
                (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < dag.nodes.size),
      P index hIndex (dag.nodeAt index hIndex) := by
  simpa [ParentsBefore, graphView, nodeAt] using
    DenseDAG.View.topologicalInduction dag.graphView hParents hStep
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem rootByTopologicalInduction (dag : DAG σ) (hRoot : dag.root < dag.nodes.size) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < dag.nodes.size), (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex) (dag.nodeAt parent
                (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    P dag.root hRoot (dag.nodeAt dag.root hRoot) :=
  by
    simpa [ParentsBefore, graphView, nodeAt] using
      DenseDAG.View.rootByTopologicalInduction
        dag.graphView hRoot hParents hStep
end DAG
structure CheckedDAG
      where
  private mkInternal ::
  dag : DAG σ
  contract : DAG.Contract dag
/-! ## HO-AVATAR 全局 registry 包装 -/
structure CheckedAvatarDAG
     where
  checked : CheckedDAG (σ := σ)
  registryChecked : checked.dag.avatarSelectorRegistryChecked = true
namespace CheckedAvatarDAG
def mk? (checked : CheckedDAG (σ := σ)) : Option (CheckedAvatarDAG (σ := σ)) :=
  if hRegistry : checked.dag.avatarSelectorRegistryChecked = true then
    some { checked := checked, registryChecked := hRegistry }
  else
    none
end CheckedAvatarDAG
namespace CheckedDAG
section CheckedDAGEnvironment
variable (cert : CheckedDAG (σ := σ)) (index : Nat) (hIndex : index < cert.dag.nodes.size)
def ofContract (dag : DAG σ) (contract : DAG.Contract dag) : CheckedDAG (σ := σ) := ⟨dag, contract⟩
theorem parentGuardsHold_of_localNodeGuardsOk (hMerge :
      DAG.payloadMergesParentGuards (cert.dag.nodeAt index hIndex).payload = true) (parent : Nat)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList) (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
      Node.GuardsHold valuation (cert.dag.nodeAt parent hParentSize).guards := by
  have hGuardCheck := (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  rw [if_pos hMerge] at hGuardCheck
  cases hUnion :
      cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hGuardCheck
  | some unionGuards =>
      have hEq :
          Guards.eq (cert.dag.nodeAt index hIndex).guards unionGuards = true := by
        simpa [hUnion] using hGuardCheck
      intro hCurrentGuards
      have hUnionGuards : Node.GuardsHold valuation unionGuards :=
        Node.GuardsHold.of_guardSetEq hEq hCurrentGuards
      intro lit hLit
      exact hUnionGuards lit (DAG.mem_parentGuardUnionList_of_parent_mem (dag := cert.dag) (parents := (cert.dag.nodeAt index hIndex).parents.toList)
          (parent := parent) (parentNode := cert.dag.nodeAt parent hParentSize) (guards := unionGuards) (lit := lit)
          (by simpa [DAG.parentGuardUnion?] using hUnion)
          hParentMem (cert.dag.node?_eq_some_nodeAt hParentSize)
          hLit)
theorem rootByTopologicalInduction
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size), (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex) (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    P cert.dag.root cert.contract.root_exists (cert.dag.nodeAt cert.dag.root cert.contract.root_exists) :=
  cert.dag.rootByTopologicalInduction cert.contract.root_exists cert.contract.parents_before hStep
end CheckedDAGEnvironment
end CheckedDAG
end HODAGCertificateSignature
end HODAGCertificate
end Automation
end YesMetaZFC
