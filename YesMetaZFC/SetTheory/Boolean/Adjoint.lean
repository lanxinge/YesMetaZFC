import YesMetaZFC.SetTheory.Boolean.CompleteHom

/-! # 完全布尔同态的规范左伴随

对 b，分离 N={a : i(a)≤¬b}，再令 π(b)=¬⋁N。
完全性给出伴随律 b≤i(a) ↔ π(b)≤a；替换将唯一投影组成实际集合函数图。
目标只需布尔代数，源只需对内部集合族完备；此构造不要求同态单射。
-/
namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Boolean_d.neg_order_l {A R z a b n m : M.Domain} (h : Boolean_d I A R z)
    (ha : M.mem a A) (hb : M.mem b A) (an : Imp_d I A R a z n) (bm : Imp_d I A R b z m) :
    M.PairMember I n m R ↔ M.PairMember I b a R := by
  obtain ⟨t,ht⟩ := h.meet n b an.1 hb
  apply (bm.adjoint_l I h.order an.1 ht).trans
  apply Iff.trans (show M.PairMember I t z R ↔ t = z from
    ⟨fun tz => h.order.antisymm t z ht.1 h.bot_mem tz (h.bot_le t ht.1),
      fun eq => eq ▸ h.order.refl z h.bot_mem⟩)
  exact (h.neg_test_l I hb ha an (meet_comm_d I ht)).symm

def Badj_d (A R B S F b a : M.Domain) : Prop := M.mem b B ∧ M.mem a A ∧
  ∀ c y, M.PairMember I c y F → (M.PairMember I b y S ↔ M.PairMember I a c R)

def badj_m (𝒞 : OrderedPairConvention) {n} (A R B S F b a : Term n) : Formula 1 n := set[n] ⟪
  ⌜b⌝ₛ ∈ ⌜B⌝ₛ ∧ ⌜a⌝ₛ ∈ ⌜A⌝ₛ ∧ (∀ c, ∀ y,
    ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(c,y,⌜F⌝ₛ) →
    (⌜(Formula.orderedPairMem 𝒞)⌝ₚ(⌜b⌝ₛ,y,⌜S⌝ₛ) ↔ ⌜(Formula.orderedPairMem 𝒞)⌝ₚ(⌜a⌝ₛ,c,⌜R⌝ₛ)))⟫
derive_free_closed badj_m

theorem badj_sat_l {n} (ρ : Env M n) (A R B S F b a : Term n) :
    Formula.satisfies ρ (badj_m 𝒞 A R B S F b a) ↔
      Badj_d I (A.eval ρ) (R.eval ρ) (B.eval ρ) (S.eval ρ) (F.eval ρ) (b.eval ρ) (a.eval ρ) := by
  simp only [badj_m,Badj_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_orderedPairMem_iff I,Definitional.Term.eval_weaken]
  rfl

theorem Badj_d.unique_l {A R B S F b a c : M.Domain} (O : Order_d I A R)
    (fn : M.IsSetFunctionFromTo I F A B) (h : Badj_d I A R B S F b a)
    (k : Badj_d I A R B S F b c) : a = c := by
  obtain ⟨x,_,ax⟩ := fn.2.2 a h.2.1
  obtain ⟨y,_,cy⟩ := fn.2.2 c k.2.1
  exact O.antisymm a c h.2.1 k.2.1
    ((h.2.2 c y cy).mp ((k.2.2 c y cy).mpr (O.refl c k.2.1)))
    ((k.2.2 a x ax).mp ((h.2.2 a x ax).mpr (O.refl a h.2.1)))

theorem Badj_d.positive_l {A R z B S w F b a : M.Domain} (L : Boolean_d I A R z)
    (K : Boolean_d I B S w) (zero : M.PairMember I z w F) (ba : Badj_d I A R B S F b a)
    (nz : b ≠ w) : a ≠ z := by
  intro eq
  have bw := (ba.2.2 z w zero).mpr (eq.symm ▸ L.order.refl z L.bot_mem)
  exact nz (K.order.antisymm b w ba.1 K.bot_mem bw (K.bot_le b ba.1))

/-- 左伴随保持内部集合族的上确界；像族由实际投影图逐条目读取。 -/
theorem Badj_d.sup_l {A R B S F P D E b a : M.Domain}
    (L : Order_d I A R) (K : Order_d I B S) (fn : M.IsSetFunctionFromTo I F A B)
    (projection : M.IsSetFunctionFromTo I P B A)
    (adj : ∀ x y, M.PairMember I x y P → Badj_d I A R B S F x y)
    (image : ∀ y, M.mem y E ↔ ∃ x, M.mem x D ∧ M.PairMember I x y P)
    (sub : M.MemberSubset D B) (sup : Bsup_d I B S D b) (ba : M.PairMember I b a P) : Bsup_d I A R E a := by
  have h := adj b a ba
  obtain ⟨t,ht,ha⟩ := fn.2.2 a h.2.1
  have bt := (h.2.2 a t ha).mpr (L.refl a h.2.1)
  refine ⟨h.2.1,?_,?_⟩
  · intro y hy
    obtain ⟨x,hx,xy⟩ := (image y).mp hy
    exact ((adj x y xy).2.2 a t ha).mp (K.trans x b t (sub x hx) sup.1 ht (sup.2.1 x hx) bt)
  · intro c hc upper
    obtain ⟨v,hv,cv⟩ := fn.2.2 c hc
    apply (h.2.2 c v cv).mp
    apply sup.2.2 v hv
    intro x hx
    obtain ⟨y,_,xy⟩ := projection.2.2 x (sub x hx)
    exact ((adj x y xy).2.2 c v cv).mpr (upper y ((image y).mpr ⟨x,hx,xy⟩))

variable (hZF : M.Models ZF)
include hZF

theorem Cbh_d.adjoint_value_l {A R z B S w F b : M.Domain} (h : Cbh_d I A R z B S w F)
    (L : Cba_d I A R z) (K : Boolean_d I B S w) (hb : M.mem b B) :
    ∃ a, Badj_d I A R B S F b a := by
  obtain ⟨n,bn⟩ := K.imp b w hb K.bot_mem
  let ρ : Env M 3 := ⟨fun i => [F,S,n].get i,fun _ => F⟩
  let φ : UnarySchema 3 := {
    body := .existsE (.conj (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
      (Formula.orderedPairMem 𝒞 .newest (.bound 4) (.bound 3))) }
  obtain ⟨N,mem⟩ := ZF.separation_exists_d hZF φ ρ A
  have members a : M.mem a N ↔ M.mem a A ∧ ∃ y, M.PairMember I a y F ∧ M.PairMember I y n S := by
    rw [mem]
    simp only [φ,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have sub : M.MemberSubset N A := fun a ha => ((members a).mp ha).1
  obtain ⟨k,sup⟩ := L.sup N sub
  obtain ⟨v,hv,kv⟩ := h.function.2.2 k sup.1
  have vn : M.PairMember I v n S := (h.sup N k v sub sup kv).2 n bn.1 (by
    intro a y ha ay
    obtain ⟨_,t,ht,tn⟩ := (members a).mp ha
    exact h.function.1.2 a t y ht ay ▸ tn)
  obtain ⟨a,ka⟩ := L.imp k z sup.1 L.bot_mem
  refine ⟨a,hb,ka.1,fun c y cy => ?_⟩
  have hc := h.function.input_mem_of_pairMember cy
  obtain ⟨d,cd⟩ := L.imp c z hc L.bot_mem
  obtain ⟨x,hx,dx⟩ := h.function.2.2 d cd.1
  obtain ⟨c',dc⟩ := L.imp d z cd.1 L.bot_mem
  have dc : Imp_d I A R d z c := L.double_neg c d c' hc cd dc ▸ dc
  apply (K.neg_order_l I (h.function.output_mem_of_pairMember cy) hb (h.neg c d y x cy dx cd) bn).symm.trans
  apply Iff.trans (show M.PairMember I x n S ↔ M.PairMember I d k R from
    ⟨fun xn => sup.2.1 d ((members d).mpr ⟨cd.1,x,dx,xn⟩),
      fun dk => K.order.trans x v n hx hv bn.1 (h.toBh_d.mono_l I L.toBoolean_d K dx kv dk) vn⟩)
  exact (L.toBoolean_d.neg_order_l I sup.1 cd.1 ka dc).symm

theorem Cbh_d.adjoint_l {A R z B S w F : M.Domain} (h : Cbh_d I A R z B S w F)
    (L : Cba_d I A R z) (K : Boolean_d I B S w) :
    ∃ P, M.IsSetFunctionFromTo I P B A ∧
      ∀ b a, M.PairMember I b a P ↔ Badj_d I A R B S F b a := by
  let ρ : Env M 5 := ⟨fun i => [A,R,B,S,F].get i,fun _ => A⟩
  let φ : BinarySchema 5 := {
    body := badj_m 𝒞 (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 1) .newest }
  have sat b a : φ.denote ρ b a ↔ Badj_d I A R B S F b a := badj_sat_l I ..
  obtain ⟨P,fn,graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := B) (target := A)
    (fun b hb => (h.adjoint_value_l I hZF L K hb).imp fun a ha => (sat b a).mpr ha)
    (fun _ _ _ _ ha hc => ((sat _ _).mp ha).unique_l I L.order h.function ((sat _ _).mp hc))
    (fun _ _ _ ha => ((sat _ _).mp ha).2.1)
  exact ⟨P,fn,fun b a => (graph b a).trans ((and_congr_right fun _ => sat b a).trans
    ⟨And.right,fun ha => ⟨ha.1,ha⟩⟩)⟩

end YesMetaZFC.SetTheory.BooleanZF
