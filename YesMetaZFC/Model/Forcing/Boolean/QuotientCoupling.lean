import YesMetaZFC.Model.Forcing.Boolean.QuotientName
import YesMetaZFC.Model.Forcing.Boolean.RegularExtension

/-! # 商分解的共同条件序

条件为 (q,x)，其中 q≤c 且 q∈π(x)。它在目标布尔代数中表示 x∧i([q])。
主正则开图和伴随图都是实际集合函数，故共同条件序及比较图亦在地模型中成集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kpair_interpretation_l M (And.left hZF) (KP.exists_pair (ZF.modelsKP hZF))

structure Qc_d (Q T w u A S e L V d J P N : M.Domain) : Prop where
  small : Cond_order_d M Q T w
  cone : Ropen_d Q T w u
  family : ∀ a, M.mem a A ↔ Ropen_d Q T w a ∧ M.MemberSubset a u
  order : ∀ a b, M.mem a A → M.mem b A → (Entry_d M a b S ↔ M.MemberSubset a b)
  empty : ∀ q, ¬ M.mem q e
  source : BooleanZF.Boolean_d I A S e
  target : BooleanZF.Boolean_d I L V d
  hom : BooleanZF.Bh_d I A S e L V d J
  projection : M.IsSetFunctionFromTo I P L A
  adjoint : ∀ x a, Entry_d M x a P → BooleanZF.Badj_d I A S L V J x a
  principal : M.IsSetFunctionFromTo I N u A
  graph : ∀ q a, Entry_d M q a N ↔ M.mem q u ∧ Rpr_d Q T w q a

def Qc_cond_d (Q T w c d P q x : M.Domain) : Prop :=
  Below_d M Q T w q c ∧ x ≠ d ∧ ∃ a, Entry_d M x a P ∧ M.mem q a

def qc_cond_m {n} (Q T w c d P q x : Term n) : Formula 1 n := set[n] ⟪
  ⌜below_m⌝ₚ(⌜Q⌝ₛ,⌜T⌝ₛ,⌜w⌝ₛ,⌜q⌝ₛ,⌜c⌝ₛ) ∧ ⌜x⌝ₛ ≠ ⌜d⌝ₛ ∧
  (∃ a, ⌜entry_m⌝ₚ(⌜x⌝ₛ,a,⌜P⌝ₛ) ∧ ⌜q⌝ₛ ∈ a)⟫
derive_free_closed qc_cond_m

include hZF

theorem qc_cond_sat_l {n} (ρ : Env M n) (Q T w c d P q x : Term n) :
    Formula.satisfies ρ (qc_cond_m Q T w c d P q x) ↔
      Qc_cond_d (Q.eval ρ) (T.eval ρ) (w.eval ρ) (c.eval ρ) (d.eval ρ) (P.eval ρ) (q.eval ρ) (x.eval ρ) := by
  simp only [qc_cond_m,Qc_cond_d,Formula.satisfies_conj_iff,below_sat_l M hZF.1,
    Formula.extensionalNe,Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_exists_iff,entry_sat_l M hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]
  rfl

structure Qcp_d (Q T w c L V d J P N C R F : M.Domain) : Prop where
  graph : ∀ v, M.mem v C → ∃ q x, KPair_d M v q x
  conditions : ∀ q x, Entry_d M q x C ↔ Qc_cond_d Q T w c d P q x
  order : ∀ v v', Entry_d M v v' R ↔ M.mem v C ∧ M.mem v' C ∧ ∃ q x q' x',
    KPair_d M v q x ∧ KPair_d M v' q' x' ∧ Entry_d M q q' T ∧ Entry_d M x x' V
  function : M.IsSetFunctionFromTo I F C L
  values : ∀ v b, Entry_d M v b F ↔ M.mem v C ∧ ∃ q x a y,
    KPair_d M v q x ∧ Entry_d M q a N ∧ Entry_d M a y J ∧ BooleanZF.Meet_d I L V x y b

variable {Q T w u A S e L V d J P N c C R F : M.Domain}

theorem Qc_d.point_cmp_l (h : Qc_d hZF Q T w u A S e L V d J P N) {a b q}
    (ha : M.mem a A) (hb : M.mem b A) (qa : M.mem q a) (qb : M.mem q b) : Cmp_d M A S e a b := by
  obtain ⟨r,hr,qr⟩ := h.principal.2.2 q (((h.family a).mp ha).2 q qa)
  have pr := ((h.graph q r).mp qr).2
  exact ⟨r,⟨hr,fun eq => h.empty q (eq ▸ pr.2.1),
    (h.order r a hr ha).mpr (pr.2.2 a ((h.family a).mp ha).1 qa)⟩,
    (h.order r b hr hb).mpr (pr.2.2 b ((h.family b).mp hb).1 qb)⟩

theorem Qc_d.conditions_l (h : Qc_d hZF Q T w u A S e L V d J P N) (c : M.Domain) :
    ∃ C R F, Qcp_d hZF Q T w c L V d J P N C R F := by
  let ρ : Env M 6 := ⟨fun i => [Q,T,w,c,d,P].get i,fun _ => Q⟩
  let φ : BinarySchema 6 := {
    body := qc_cond_m (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 1) .newest }
  have sat q x : φ.denote ρ q x ↔ Qc_cond_d Q T w c d P q x := qc_cond_sat_l hZF ..
  obtain ⟨U,union⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) Q L
  obtain ⟨C,clean,graph⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ U
  have conditions q x : Entry_d M q x C ↔ Qc_cond_d Q T w c d P q x := by
    apply (graph q x).trans
    rw [sat]
    refine ⟨fun hh => hh.2.2,fun hh => ?_⟩
    obtain ⟨a,xa,_⟩ := hh.2.2
    exact ⟨(union q).mpr (Or.inl hh.1.1),(union x).mpr (Or.inr (h.projection.input_mem_of_pairMember xa)),hh⟩
  let η : Env M 2 := ⟨Fin.cases T (fun _ => V),fun _ => T⟩
  let ψ : BinarySchema 2 := { body := set[4] ⟪ ∃ q, ∃ x, ∃ q', ∃ x',
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 4)⌝ₛ,q,x) ∧ ⌜kpair_m⌝ₚ(⌜(.newest : Term 4)⌝ₛ,q',x') ∧
    ⌜entry_m⌝ₚ(q,q',⌜(.bound 2 : Term 4)⌝ₛ) ∧ ⌜entry_m⌝ₚ(x,x',⌜(.bound 3 : Term 4)⌝ₛ)⟫ }
  have satOrder v v' : ψ.denote η v v' ↔ ∃ q x q' x', KPair_d M v q x ∧ KPair_d M v' q' x' ∧
      Entry_d M q q' T ∧ Entry_d M x x' V := by
    simp only [BinarySchema.denote,ψ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,entry_sat_l M hZF.1,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨R,_,edges⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η C
  let δ : Env M 4 := ⟨fun i => [N,J,L,V].get i,fun _ => N⟩
  let χ : BinarySchema 4 := { body := set[6] ⟪ ∃ q, ∃ x, ∃ a, ∃ y,
    ⌜kpair_m⌝ₚ(⌜(.bound 1 : Term 6)⌝ₛ,q,x) ∧ ⌜entry_m⌝ₚ(q,a,⌜(.bound 2 : Term 6)⌝ₛ) ∧
    ⌜entry_m⌝ₚ(a,y,⌜(.bound 3 : Term 6)⌝ₛ) ∧
    ⌜(BooleanZF.meet_m kpair_convention_l)⌝ₚ(⌜(.bound 4 : Term 6)⌝ₛ,⌜(.bound 5 : Term 6)⌝ₛ,x,y,⌜(.newest : Term 6)⌝ₛ)⟫ }
  have satMap v b : χ.denote δ v b ↔ ∃ q x a y, KPair_d M v q x ∧ Entry_d M q a N ∧
      Entry_d M a y J ∧ BooleanZF.Meet_d I L V x y b := by
    simp only [BinarySchema.denote,χ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      kpair_sat_l M hZF.1,entry_sat_l M hZF.1,BooleanZF.meet_sat_d I,Definitional.Term.eval_weaken]
    rfl
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I χ δ (source := C) (target := L) (fun v hv => by
    obtain ⟨q,x,pair⟩ := clean.1 v hv
    obtain ⟨_,_,b,xb,qb⟩ := (conditions q x).mp ⟨v,pair,hv⟩
    obtain ⟨a,ha,qa⟩ := h.principal.2.2 q (((h.family b).mp (h.projection.output_mem_of_pairMember xb)).2 q qb)
    obtain ⟨y,hy,ay⟩ := h.hom.function.2.2 a ha
    obtain ⟨m,meet⟩ := h.target.meet x y (h.projection.input_mem_of_pairMember xb) hy
    exact ⟨m,(satMap v m).mpr ⟨q,x,a,y,pair,qa,ay,meet⟩⟩) (by
      intro v _ b b' hb hb'
      obtain ⟨q,x,a,y,pair,qa,ay,meet⟩ := (satMap v b).mp hb
      obtain ⟨q',x',a',y',pair',qa',ay',meet'⟩ := (satMap v b').mp hb'
      obtain ⟨qq,xx⟩ := kpair_injective_l M pair pair'
      subst q' x'
      have aa := h.principal.1.2 q a a' qa qa'
      subst a'
      have yy := h.hom.function.1.2 a y y' ay ay'
      subst y'
      exact meet.unique_l I h.target.order meet') (by
      intro v b _ hb
      obtain ⟨_,_,_,_,_,_,_,meet⟩ := (satMap v b).mp hb
      exact meet.1)
  exact ⟨C,R,F,clean.1,conditions,fun v v' => (edges v v').trans
    (and_congr_right fun _ => and_congr_right fun _ => satOrder v v'),fn,
    fun v b => (values v b).trans (and_congr_right fun _ => satMap v b)⟩

end YesMetaZFC.Model.Forcing.Internal
