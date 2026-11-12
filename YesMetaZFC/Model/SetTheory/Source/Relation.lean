import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceComposition

/-! # 源内函数值族的逐点求值

把两份源内代表在指定好集合上复合，坏坐标取同一个源内对象。所有候选
函数值由函数值族的一次并和坐标包络界住，因此只用已有的有界统一化。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_apply_on_l {ω c X R D A f x : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (model : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (hD : M.mem D X) (hA : M.mem A X)
    (hf : M.mem f X) (ff : Fn0_d D X f) (hx : M.mem x X) (fx : Fn0_d D X x)
    (total : ∀ s, M.mem s A → ∃ t z y, Rd_entry_d s t f ∧ Rd_entry_d s z x ∧ Rd_entry_d z y t) :
    ∃ g, M.mem g X ∧ Fn0_d D X g ∧
      ∀ s t z y, M.mem s A → Rd_entry_d s t f → Rd_entry_d s z x → Rd_entry_d s y g → Rd_entry_d z y t := by
  obtain ⟨B, hB, bound⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).envelope_l hf
  obtain ⟨H, hH, un⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).union B hB
  obtain ⟨C, hC, coords⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).envelope_l hH
  obtain ⟨P, hP, boundX⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).envelope_l hx
  obtain ⟨Q, hQ, insert⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX model).insert_l hC hD
  have inside t z y (ht : M.mem t B) (entry : Rd_entry_d z y t) : M.mem y C := by
    obtain ⟨p, pair, hp⟩ := entry
    exact (coords z y ⟨p, pair, (un p).mpr ⟨t, ht, hp⟩⟩).2
  let ρ : Env M 6 := ⟨fun i => [f, x, A, B, P, D].get i, fun _ => D⟩
  let φ : BinarySchema 6 := {
    body := .disj
      (.conj (.mem (.bound 1) (.bound 4)) (Formula.existsMem (.bound 5) (Formula.existsMem (.bound 7)
        (.conj (rd_entry0_m (.bound 3) (.bound 1) (.bound 4))
          (.conj (rd_entry0_m (.bound 3) .newest (.bound 5)) (rd_entry0_m .newest (.bound 2) (.bound 1)))))))
      (.conj (.neg (.mem (.bound 1) (.bound 4))) (Formula.extensionalEq .newest (.bound 7))) }
  have read s y : φ.denote ρ s y ↔
      (M.mem s A ∧ ∃ t, M.mem t B ∧ ∃ z, M.mem z P ∧ Rd_entry_d s t f ∧ Rd_entry_d s z x ∧ Rd_entry_d z y t) ∨
      (¬ M.mem s A ∧ y = D) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have params : ∀ i, M.mem (ρ.bound i) X :=
    Fin.cases hf (Fin.cases hx (Fin.cases hA (Fin.cases hB (Fin.cases hP (Fin.cases hD (fun i => Fin.elim0 i))))))
  obtain ⟨g, hg, fg, choose⟩ := sc_uniform_source_l hZF hω hX model theory φ
    (.disj (.conj (.mem _ _) (.existsMem _ (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))) (.conj (.neg (.mem _ _)) (.atom ..)))
    ρ params hD hQ (fun s _ => by
      classical
      by_cases hs : M.mem s A
      · obtain ⟨t, z, y, hst, hsz, hzy⟩ := total s hs
        exact ⟨y, (insert y).mpr (Or.inl (inside t z y (bound s t hst).2 hzy)),
          (read s y).mpr (Or.inl ⟨hs, t, (bound s t hst).2, z, (boundX s z hsz).2, hst, hsz, hzy⟩)⟩
      · exact ⟨D, (insert D).mpr (Or.inr rfl), (read s D).mpr (Or.inr ⟨hs, rfl⟩)⟩)
  refine ⟨g, hg, fg.mono_target_l (hX Q hQ), fun s t z y hs hst hsz hsy => ?_⟩
  rcases (read s y).mp (choose s y hsy) with ⟨_, t', _, z', _, hst', hsz', hzy⟩ | ⟨no, _⟩
  · exact (fn0_function_l (ZF.modelsKP hZF) ff).1.2 s t' t hst' hst ▸
      (fn0_function_l (ZF.modelsKP hZF) fx).1.2 s z' z hsz' hsz ▸ hzy
  · exact (no hs).elim

end YesMetaZFC.SetTheory.Internal

/-! ## 向源内枚举加入指定参数

只移动自然数坐标：新参数占零，原自然数坐标移到后继，其余坐标不动。
因此保持原字母表，无须背景基数正确性，也不向源要求完整函数空间。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_insert_enumeration_l {ω c Z R κ A f x : M.Domain} (hω : M.IsOmega ω)
    (hZ : M.TransitiveSet Z) (hm : Smem_d I c Z R) (theory : Sc_theory_d I ω Z R)
    (hωZ : M.mem ω Z) (hκZ : M.mem κ Z) (hωκ : M.MemberSubset ω κ)
    (hA : M.mem A Z) (hf : M.mem f Z) (hx : M.mem x Z) (bij : M.IsSetBijectionFromTo I f κ A) :
    ∃ B g, M.mem B Z ∧ M.mem g Z ∧ (∀ y, M.mem y B ↔ M.mem y A ∨ y = x) ∧ M.IsSetBijectionFromTo I g κ B := by
  classical
  obtain ⟨B, hB, insert⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hZ hm).insert_l hA hx
  by_cases hxA : M.mem x A
  · have eq := hZF.1.eq_of_same_members A B (fun y => ⟨fun h => (insert y).mpr (Or.inl h),
      fun h => ((insert y).mp h).elim id (fun e => e ▸ hxA)⟩)
    exact ⟨B, f, hB, hf, insert, eq ▸ bij⟩
  obtain ⟨z, hz, hzω⟩ := hω.1.1
  let shift i m := (M.mem m ω ∧ M.SuccessorOf i m) ∨ (¬ M.mem m ω ∧ i = m)
  have succω i m (hm : M.mem m ω) (hs : M.SuccessorOf i m) : M.mem i ω := by
    obtain ⟨j, hj, hjω⟩ := hω.1.2 m hm
    exact Structure.SuccessorOf.eq hZF.1 hj hs ▸ hjω
  have input i m n (h : shift i m) (k : shift i n) : m = n := by
    rcases h with ⟨hm, hs⟩ | ⟨hm, rfl⟩ <;> rcases k with ⟨hn, ht⟩ | ⟨hn, he⟩
    · exact Structure.SuccessorOf.predecessor_eq hZF.1 ((hω.isOrdinal (ZF.modelsKP hZF)).mem hm) hs ht
    · exact (hn (he ▸ succω i m hm hs)).elim
    · exact (hm (succω _ n hn ht)).elim
    · exact he
  have output i j m (h : shift i m) (k : shift j m) : i = j := by
    rcases h with ⟨hm, hs⟩ | ⟨hm, hi⟩ <;> rcases k with ⟨hn, ht⟩ | ⟨hn, hj⟩
    · exact Structure.SuccessorOf.eq hZF.1 hs ht
    · exact (hn hm).elim
    · exact (hm hn).elim
    · exact hi.trans hj.symm
  let φ : BinarySchema 5 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 5)) (Formula.extensionalEq .newest (.bound 4)))
      (Formula.existsMem (.bound 6) (.conj (rd_entry0_m .newest (.bound 1) (.bound 3))
        (.disj (.conj (.mem .newest (.bound 4)) (KP.succ0_m (.bound 2) .newest))
          (.conj (.neg (.mem .newest (.bound 4))) (Formula.extensionalEq (.bound 2) .newest))))) }
  let ρ : Env M 5 := ⟨Fin.cases f (Fin.cases ω (Fin.cases x (Fin.cases z (fun _ => κ)))), fun _ => z⟩
  have read i y : φ.denote ρ i y ↔ (i = z ∧ y = x) ∨ ∃ m, M.mem m κ ∧ Rd_entry_d m y f ∧ shift i m := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_mem_iff, KP.succ0_sat_l hZF.1, Formula.satisfies_neg_iff]; rfl
  have zero m : ¬ shift z m := fun h => h.elim
    (fun h => hz m h.2.predecessor_mem) (fun h => h.1 (h.2 ▸ hzω))
  have unique i y v (hy : φ.denote ρ i y) (hv : φ.denote ρ i v) : y = v := by
    rcases (read i y).mp hy with ⟨rfl, rfl⟩ | ⟨m, _, hmy, hs⟩ <;>
      rcases (read _ v).mp hv with ⟨he, hv⟩ | ⟨n, _, hnv, ht⟩
    · exact hv.symm
    · exact (zero n ht).elim
    · exact (zero m (he ▸ hs)).elim
    · exact bij.1.1.1.2 m y v hmy (input i m n hs ht ▸ hnv)
  have total i (hi : M.mem i κ) : ∃ y, M.mem y B ∧ φ.denote ρ i y := by
    by_cases hi0 : i = z
    · exact ⟨x, (insert x).mpr (Or.inr rfl), (read i x).mpr (Or.inl ⟨hi0, rfl⟩)⟩
    have prev : ∃ m, M.mem m κ ∧ shift i m := by
      by_cases hiω : M.mem i ω
      · have ne : ∃ a, M.mem a i := Classical.byContradiction (fun no => hi0 (hZF.1.eq_of_same_members i z
          (fun a => iff_of_false (fun ha => no ⟨a, ha⟩) (hz a))))
        obtain ⟨m, hm, hs⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF hiω ne
        exact ⟨m, hωκ m hm, Or.inl ⟨hm, hs⟩⟩
      · exact ⟨i, hi, Or.inr ⟨hiω, rfl⟩⟩
    obtain ⟨m, hm, hs⟩ := prev
    obtain ⟨y, hy, hmy⟩ := bij.1.1.2.2 m hm
    exact ⟨y, (insert y).mpr (Or.inl hy), (read i y).mpr (Or.inr ⟨m, hm, hmy, hs⟩)⟩
  obtain ⟨g, hg, fn, select⟩ := sc_uniform_source_l hZF hω hZ hm theory φ
    (.disj (.conj (.atom ..) (.atom ..)) (.existsMem _ (.conj (rd_entry0_delta_l ..)
      (.disj (.conj (.mem _ _) (KP.succ0_delta_l ..)) (.conj (.neg (.mem _ _)) (.atom ..)))))) ρ
    (Fin.cases hf (Fin.cases hωZ (Fin.cases hx (Fin.cases (hZ ω hωZ z hzω) (fun _ => hκZ))))) hκZ hB total
  refine ⟨B, g, hB, hg, insert, ⟨fn0_function_l (ZF.modelsKP hZF) fn, ?_⟩, fun y hy => ?_⟩
  · intro i j y hi hj
    rcases (read i y).mp (select i y hi) with ⟨hi0, rfl⟩ | ⟨m, _, hmy, hs⟩ <;>
      rcases (read j _).mp (select j _ hj) with ⟨hj0, he⟩ | ⟨n, _, hny, ht⟩
    · exact hi0.trans hj0.symm
    · exact (hxA (bij.1.1.output_mem_of_pairMember hny)).elim
    · exact (hxA (he ▸ bij.1.1.output_mem_of_pairMember hmy)).elim
    · exact output i j m hs (bij.1.2 m n y hmy hny ▸ ht)
  · have pre : ∃ i, M.mem i κ ∧ φ.denote ρ i y := by
      rcases (insert y).mp hy with hy | rfl
      · obtain ⟨m, hm, hmy⟩ := bij.2 y hy
        by_cases hmω : M.mem m ω
        · obtain ⟨i, hs, hiω⟩ := hω.1.2 m hmω
          exact ⟨i, hωκ i hiω, (read i y).mpr (Or.inr ⟨m, hm, hmy, Or.inl ⟨hmω, hs⟩⟩)⟩
        · exact ⟨m, hm, (read m y).mpr (Or.inr ⟨m, hm, hmy, Or.inr ⟨hmω, rfl⟩⟩)⟩
      · exact ⟨z, hωκ z hzω, (read z y).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    obtain ⟨i, hi, val⟩ := pre
    obtain ⟨v, _, hiv⟩ := fn.2.1 i hi
    exact ⟨i, hi, unique i v y (select i v hiv) val ▸ hiv⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 有界分离族的源内函数图

先把各行的成员关系放入已有乘积，再取实际纤维族。函数值是这些纤维，
所以不要求源拥有完整幂集，也不对任意定义域作无界统一化。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_fiber_function_l {ω c X R D P : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hP : M.mem P X) : ∃ F C, M.mem F X ∧ M.mem C X ∧ Fn0_d D C F ∧
      ∀ d t, Rd_entry_d d t F ↔ M.mem d D ∧ Rd_fiber_d P d t := by
  obtain ⟨C, hC, fibers⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).fibers P D hP hD
  let φ : BinarySchema 1 := { body := rd_fiber0_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  have sat d t : φ.denote ρ d t ↔ Rd_fiber_d P d t := rd_fiber0_sat_l hZF.1 ..
  obtain ⟨F, hF, hf, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ (rd_fiber0_delta_l ..)
    ρ (fun _ => hP) hD hC (fun d hd => by
      obtain ⟨t, ht⟩ := rd_fiber_exists_l (ZF.modelsKP hZF) P d
      exact ⟨t, (fibers t).mpr ⟨d, hd, ht⟩, (sat d t).mpr ht⟩)
  refine ⟨F, C, hF, hC, hf, fun d t => ⟨fun h => ⟨(hf.bound_l h).1, (sat d t).mp (select d t h)⟩, ?_⟩⟩
  rintro ⟨hd, ht⟩
  obtain ⟨u, _, hdu⟩ := hf.2.1 d hd
  exact hZF.1.eq_of_same_members u t (fun x => ((sat d u).mp (select d u hdu) x).trans (ht x).symm) ▸ hdu

theorem sc_separation_function_l {ω c X R D A : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    {p} (φ : BinarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p) (hρ : ∀ i, M.mem (ρ.bound i) X)
    (hD : M.mem D X) (hA : M.mem A X) : ∃ F C, M.mem F X ∧ M.mem C X ∧ Fn0_d D C F ∧
      ∀ d t, Rd_entry_d d t F → ∀ x, M.mem x t ↔ M.mem x A ∧ φ.denote ρ d x := by
  let e : Fin (p+2) → Fin (p+2) := Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))
  let ψ : BinarySchema p := {
    body := φ.body.rename e
    freeClosed := (Definitional.Formula.freeClosed_rename e φ.body).mpr φ.freeClosed }
  have sat x d : ψ.denote ρ x d ↔ φ.denote ρ d x :=
    (Formula.satisfies_rename ..).trans (Formula.closed_env_l φ.body φ.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  obtain ⟨Q, hQX, _, spec⟩ := sc_relation_source_l hZF hω hX hm theory ψ (hd.rename_l e) ρ hρ hA hD
  obtain ⟨F, C, hF, hC, hf, fibers⟩ := sc_fiber_function_l hZF hω hX hm theory hD hQX
  exact ⟨F, C, hF, hC, hf, fun d t hdt x => ((fibers d t).mp hdt).2 x |>.trans ((spec x d).trans
    ⟨fun ⟨hx, _, h⟩ => ⟨hx, (sat x d).mp h⟩,
      fun ⟨hx, h⟩ => ⟨hx, (hf.bound_l hdt).1, (sat x d).mpr h⟩⟩)⟩

/-- 反向图由已有图在实际乘积中的有界分离恢复，故同一个逆图仍属于源。 -/
theorem sc_inverse_mem_l {ω c X R A B f g : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hA : M.mem A X) (hB : M.mem B X) (hf : M.mem f X) (fn : Fn0_d B A g)
    (inverse : ∀ b a, Rd_entry_d b a g ↔ Rd_entry_d a b f) : M.mem g X := by
  let ρ : Env M 1 := ⟨fun _ => f, fun _ => f⟩
  let φ : BinarySchema 1 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  have sat b a : φ.denote ρ b a ↔ Rd_entry_d a b f := rd_entry0_sat_l hZF.1 ..
  obtain ⟨G, hG, shape, gs⟩ := sc_relation_source_l hZF hω hX hm theory φ (rd_entry0_delta_l ..) ρ (fun _ => hf) hB hA
  have eq := (fn0_function_l (ZF.modelsKP hZF) fn).1.1.eq_of_pairMember_iff hZF.1 shape (fun b a =>
    ⟨fun h => (gs b a).mpr ⟨(fn.bound_l h).1, (fn.bound_l h).2, (sat b a).mpr ((inverse b a).mp h)⟩,
      fun h => (inverse b a).mpr ((sat b a).mp ((gs b a).mp h).2.2)⟩)
  exact eq.symm ▸ hG

end YesMetaZFC.SetTheory.Internal

/-! ## 源内部的实际坐标重排图

给定 q:m→n 及两个实际函数空间，在源中构造 t(s)=s∘q。坐标长度不必是
外部有限数；这里甚至只要求给定域、值域和函数空间。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_reindex_l {ω c X R m n κ q D E} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hmX : M.mem m X) (hnX : M.mem n X) (hκX : M.mem κ X) (hqX : M.mem q X) (hEX : M.mem E X)
    (hq : Fn0_d m n q) (hD : ∀ s, M.mem s D ↔ Fn0_d m κ s) (hE : ∀ s, M.mem s E ↔ Fn0_d n κ s) :
    ∃ t, M.mem t X ∧ Fn0_d E D t ∧ ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r := by
  let ρ : Env M 4 := ⟨Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m))), fun _ => m⟩
  let φ : BinarySchema 4 := {
    body := Formula.existsMem (.bound 5) (Formula.existsMem (.bound 4) (Formula.existsMem (.bound 6)
      (.conj (kpair0_m (.bound 3) (.bound 2) (.bound 1))
        (.conj (rd_entry0_m (.bound 2) .newest (.bound 5)) (rd_entry0_m .newest (.bound 1) (.bound 4)))))) }
  have sat s p : φ.denote ρ s p ↔ ∃ i, M.mem i m ∧ ∃ x, M.mem x κ ∧ ∃ j, M.mem j n ∧
      KPair_d M p i x ∧ Rd_entry_d i j q ∧ Rd_entry_d j x s := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, rd_entry0_sat_l hZF.1]; rfl
  obtain ⟨P, hPX, product⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).product m κ hmX hκX
  obtain ⟨t, C, htX, _, hTC, row⟩ := sc_separation_function_l hZF hω hX hm theory φ
    (.existsMem _ (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))))
    ρ (Fin.cases hqX (Fin.cases hκX (Fin.cases hnX (fun _ => hmX)))) hEX hPX
  have read s u (hsu : Rd_entry_d s u t) : Cp0_d m n κ q s u := by
    have hs := (hE s).mp (hTC.bound_l hsu).1
    obtain ⟨r, hr⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hs
    have eq : u = r := hZF.1.eq_of_same_members u r fun p => by
      rw [row s u hsu p, sat s p]
      constructor
      · rintro ⟨_, i, _, x, _, j, _, code, hij, hjx⟩
        obtain ⟨v, hv, hvR⟩ := (hr.value_l hq hs hij).mpr hjx
        exact kpair_unique_l M hZF.1 hv code ▸ hvR
      · intro hp
        obtain ⟨i, hi, x, hx, code⟩ := hr.1.1 p hp
        obtain ⟨j, hj, hij⟩ := hq.2.1 i hi
        exact ⟨(product p).mpr ⟨i, hi, x, hx, code⟩, i, hi, x, hx, j, hj, code, hij,
          (hr.value_l hq hs hij).mp ⟨p, code, hp⟩⟩
    exact eq.symm ▸ hr
  refine ⟨t, htX, hTC.retarget_l (fun s r h => (hD r).mpr (read s r h).1), fun s r => ⟨?_, ?_⟩⟩
  · exact fun h => ⟨(hTC.bound_l h).1, read s r h⟩
  · rintro ⟨hs, hr⟩
    obtain ⟨r', _, hsr⟩ := hTC.2.1 s hs
    exact cp0_unique_l hZF.1 hq ((hE s).mp hs) (read s r' hsr) hr ▸ hsr

end YesMetaZFC.SetTheory.Internal

/-! ## 源内全相对分离得到有界载体上的实际关系

原公式中的无界量词仍在源中解释；载体及有序对图由已有源代数提供。
因此能分离“源中不存在下降枝”等全公式，而不把这种真值误当作绝对真值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_relation_relative_l {ω c X R B : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hn : Nonempty {x // M.mem x X}) {p} (φ : BinarySchema p) (ρ : Env (rt_model_l X hn) p)
    (hB : M.mem B X) : ∃ Q, M.mem Q X ∧ M.IsSetRelationOn I Q B ∧
      ∀ x y : (rt_model_l X hn).Domain, Rd_entry_d x.val y.val Q ↔
        M.mem x.val B ∧ M.mem y.val B ∧ φ.denote ρ x y := by
  obtain ⟨P, hP, product⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).product B B hB hB
  let η := ρ.push ⟨B, hB⟩
  let e : Fin (p+2) → Fin (p+4) := Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ.succ))
  let ψ : UnarySchema (p+1) := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 2)
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (φ.body.rename e)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have point (q x y : (rt_model_l X hn).Domain) :
      Formula.satisfies (((η.push q).push x).push y) (φ.body.rename e) ↔ φ.denote ρ x y :=
    (Formula.satisfies_rename ..).trans (Formula.closed_env_l φ.body φ.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  have pair (q x y : (rt_model_l X hn).Domain) : Formula.satisfies (((η.push q).push x).push y)
      (kpair0_m (.bound 2) (.bound 1) .newest) ↔ KPair_d M q.val x.val y.val :=
    (rt_model_delta_l hX hn (kpair0_delta_l ..) _).trans (kpair0_sat_l hZF.1 ..)
  have sat (q : (rt_model_l X hn).Domain) : ψ.denote η q ↔
      ∃ x : (rt_model_l X hn).Domain, M.mem x.val B ∧ ∃ y : (rt_model_l X hn).Domain,
        M.mem y.val B ∧ KPair_d M q.val x.val y.val ∧ φ.denote ρ x y := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, pair, point]; rfl
  obtain ⟨Q, hQ, sub, spec⟩ := sc_separate_relative_l I hZF hω hX hm theory hn ψ η hP
  have bounds x y (h : Rd_entry_d x y Q) : M.mem x B ∧ M.mem y B := by
    obtain ⟨q, code, hq⟩ := h
    obtain ⟨a, ha, b, hb, code'⟩ := (product q).mp (sub q hq)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code' code
    exact ⟨ha, hb⟩
  refine ⟨Q, hQ, ⟨fun q hq => ((product q).mp (sub q hq)).elim fun x hx =>
    hx.2.elim fun y hy => ⟨x, y, hy.2⟩, bounds⟩, fun x y => ⟨?_, ?_⟩⟩
  · intro h
    obtain ⟨q, code, hq⟩ := h
    obtain ⟨a, ha, b, hb, pair, val⟩ := (sat ⟨q, hX Q hQ q hq⟩).mp ((spec ⟨q, hX Q hQ q hq⟩).mp hq).2
    obtain ⟨ea, eb⟩ := kpair_injective_l M pair code
    have eax : a = x := Subtype.ext ea
    have eby : b = y := Subtype.ext eb
    subst a b
    exact ⟨ha, hb, val⟩
  · rintro ⟨hx, hy, val⟩
    obtain ⟨q, code⟩ := (I).total x.val y.val
    have hq : M.mem q P := (product q).mpr ⟨x.val, hx, y.val, hy, code⟩
    exact ⟨q, code, (spec ⟨q, hX P hP q hq⟩).mpr ⟨hq,
      (sat ⟨q, hX P hP q hq⟩).mpr ⟨x, hx, y, hy, code, val⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
