import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource
import YesMetaZFC.Model.SetTheory.Embedding.PredicateTrace
import YesMetaZFC.SetTheory.Card.FiniteSequenceSyntax
import YesMetaZFC.SetTheory.InnerModel.Recursion.Composition

/-! # 源模型包含全部背景内部有限函数

每一步只用配对和并集追加末项，再由外延性识别为背景给定图。
先收集给定函数在 ω 上的全部限制，再对该集合内的限制作 Δ₀ 归纳，覆盖非标准有限长度。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

theorem sc_finite_function_l {ω X A n f : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X)
    (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
    (union : ∀ a, M.mem a X → ∃ p, M.mem p X ∧ M.IsUnionOf p a)
    (hωX : M.mem ω X) (hA : M.MemberSubset A X) (hn : M.mem n ω) (hf : Fn0_d n A f) : M.mem f X := by
  -- 收集原图的全部有限限制；归纳量词随后都限定于这一实际集合。
  let η : Env M 2 := ⟨Fin.cases A (fun _ => f), fun _ => f⟩
  let ψ : Delta0BinarySchema 2 := {
    body := res0_m .newest (.bound 3) (.bound 1) (.bound 2)
    delta0 := res0_delta_l .. }
  have read k g : ψ.toBinarySchema.denote η k g ↔ Res0_d g f k A := by
    simp only [ψ, BinarySchema.denote, res0_sat_l hKP.1]; rfl
  obtain ⟨G, collected⟩ := KP.collection_exists_d hKP ψ η ω (fun k _ =>
    (res0_exists_l hKP f k A).imp (fun g hg => (read k g).mpr hg))
  have restrict k (hk : M.mem k ω) : ∃ g, M.mem g G ∧ Res0_d g f k A :=
    (collected k hk).imp (fun g hg => ⟨hg.1, (read k g).mp hg.2⟩)
  let ρ : Env M 5 := ⟨Fin.cases X (Fin.cases G (Fin.cases f (Fin.cases A (fun _ => n)))), fun _ => f⟩
  let φ : Delta0UnarySchema 5 := {
    body := .imp (Formula.subset .newest (.bound 5)) (Formula.forallMem (.bound 2)
      (.imp (res0_m .newest (.bound 4) (.bound 1) (.bound 5)) (.mem .newest (.bound 2))))
    delta0 := .imp (.atom ..) (.forallMem _ (.imp (res0_delta_l ..) (.mem ..))) }
  have sat k : φ.toUnarySchema.denote ρ k ↔
      (M.MemberSubset k n → ∀ g, M.mem g G → Res0_d g f k A → M.mem g X) := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
      Formula.satisfies_forallMem_iff, res0_sat_l hKP.1, Formula.satisfies_mem_iff]; rfl
  have all : ∀ k, M.mem k ω → φ.toUnarySchema.denote ρ k := by
    apply hω.induction (fun k => φ.toUnarySchema.denote ρ k) (KP.separation_exists_d hKP φ ρ ω)
    · intro z hz
      apply (sat z).mpr
      intro _ g _ hg
      obtain ⟨e, he, heω⟩ := hω.1.1
      have eq : g = e := hKP.1.eq_of_same_members g e (fun p => iff_of_false
        (fun hp => (hg.2.1 p hp).elim fun i hi => hz i hi.1) (he p))
      exact eq.symm ▸ hX ω hωX e heω
    · intro k hk ih m hs
      apply (sat m).mpr
      intro sub t _ ht
      have km : M.MemberSubset k m := fun i hi => (hs i).mpr (Or.inl hi)
      have kn : M.MemberSubset k n := fun i hi => sub i (km i hi)
      obtain ⟨g, hgG, lower⟩ := restrict k hk
      have hgX := (sat k).mp ih kn g hgG lower
      have lower := res0_restriction_l hKP hf lower
      have upper := res0_restriction_l hKP hf ht
      have hf := fn0_of_function_l hKP (upper.isSetFunctionFromTo (fn0_function_l hKP hf) sub)
      have hg : M.IsRestrictionOf I g t k := ⟨lower.1, fun a b => (lower.2 a b).trans
        ⟨fun ⟨ha, hab⟩ => ⟨ha, (upper.2 a b).mpr ⟨km a ha, hab⟩⟩,
          fun ⟨ha, hab⟩ => ⟨ha, ((upper.2 a b).mp hab).2⟩⟩⟩
      obtain ⟨x, hx, hkx⟩ := hf.2.1 k hs.predecessor_mem
      have hkX := hX ω hωX k hk
      obtain ⟨s, hsX, singleton⟩ := pair k k hkX hkX
      obtain ⟨b, hbX, both⟩ := pair k x hkX (hA x hx)
      obtain ⟨p, hpX, outer⟩ := pair s b hsX hbX
      have hp : KPair_d M p k x := ⟨s, b,
        fun y => (singleton y).trans ⟨fun h => h.elim id id, Or.inl⟩, both, outer⟩
      obtain ⟨q, hqX, one⟩ := pair p p hpX hpX
      obtain ⟨r, hrX, two⟩ := pair g q hgX hqX
      obtain ⟨f', hfX, un⟩ := union r hrX
      have graph y : M.mem y f' ↔ M.mem y g ∨ y = p := by
        rw [un]
        exact ⟨fun ⟨z, hz, hy⟩ => ((two z).mp hz).elim
          (fun e => Or.inl (e ▸ hy)) (fun e => Or.inr (((one y).mp (e ▸ hy)).elim id id)),
          fun h => h.elim (fun hy => ⟨g, (two g).mpr (Or.inl rfl), hy⟩)
            (fun e => ⟨q, (two q).mpr (Or.inr rfl), (one y).mpr (Or.inl e)⟩)⟩
      have eq : f' = t := by
        apply hKP.1.eq_of_same_members
        intro y
        rw [graph]
        constructor
        · rintro (hy | rfl)
          · obtain ⟨i, z, code⟩ := hg.1 y hy
            obtain ⟨p', pp, mem⟩ := ((hg.2 i z).mp ⟨y, code, hy⟩).2
            exact kpair_unique_l M hKP.1 pp code ▸ mem
          · obtain ⟨p', pp, mem⟩ := hkx
            exact kpair_unique_l M hKP.1 pp hp ▸ mem
        · intro hy
          obtain ⟨i, hi, z, hz, code⟩ := hf.1 y hy
          rcases (hs i).mp hi with hin | eq
          · obtain ⟨p', pp, mem⟩ := (hg.2 i z).mpr ⟨hin, y, code, hy⟩
            exact Or.inl (kpair_unique_l M hKP.1 pp code ▸ mem)
          · have eq := hKP.1.eq_of_same_members i k eq
            subst i
            have eq := hf.2.2 k hs.predecessor_mem z hz x hx ⟨y, code, hy⟩ hkx
            exact Or.inr (kpair_unique_l M hKP.1 (eq ▸ code) hp)
      exact eq ▸ hfX
  obtain ⟨g, hg, rest⟩ := restrict n hn
  have hgX := (sat n).mp (all n hn) (fun _ h => h) g hg rest
  have eq : g = f := hKP.1.eq_of_same_members g f (fun p => ⟨rest.1 p, fun hp => by
    obtain ⟨i, hi, x, hx, code⟩ := hf.1 p hp
    obtain ⟨q, hq, hqg⟩ := (rest.2.2 i hi x hx).mpr ⟨p, code, hp⟩
    exact kpair_unique_l M hKP.1 hq code ▸ hqg⟩)
  exact eq ▸ hgX

end YesMetaZFC.SetTheory.Internal

/-! ## 有限定义域上的部分图属于源

先在有限序数上补成总图，再用源内定义域取回原限制。只使用已有有限函数
闭性及有界分离，不假定源对任意外部子集封闭。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_finite_partial_l {ω c X R D n f : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hωX : M.mem ω X) (hD : M.mem D X) (hn : M.mem n ω) (sub : M.MemberSubset D n)
    (hf : Fn0_d D X f) : M.mem f X := by
  let ρ : Env M 3 := ⟨Fin.cases D (Fin.cases f (fun _ => ω)), fun _ => ω⟩
  let φ : BinarySchema 3 := {
    body := .disj (.conj (.mem (.bound 1) (.bound 2)) (rd_entry0_m (.bound 1) .newest (.bound 3)))
      (.conj (.neg (.mem (.bound 1) (.bound 2))) (Formula.extensionalEq .newest (.bound 4))) }
  have read a b : φ.denote ρ a b ↔ (M.mem a D ∧ Rd_entry_d a b f) ∨ (¬ M.mem a D ∧ b = ω) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  obtain ⟨g, fg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := n) (target := X)
    (fun a _ => by
      classical
      by_cases ha : M.mem a D
      · obtain ⟨b, _, hb⟩ := hf.2.1 a ha
        exact ⟨b, (read a b).mpr (Or.inl ⟨ha, hb⟩)⟩
      · exact ⟨ω, (read a ω).mpr (Or.inr ⟨ha, rfl⟩)⟩)
    (fun a _ b c hb hc => by
      rcases (read a b).mp hb with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        rcases (read a c).mp hc with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · exact (fn0_function_l (ZF.modelsKP hZF) hf).1.2 a b c hb hb'
      · exact (ha' ha).elim
      · exact (ha ha').elim
      · exact hb.trans hb'.symm)
    (fun a b _ hb => ((read a b).mp hb).elim (fun h => (hf.bound_l h.2).2) (fun h => h.2.symm ▸ hωX))
  have hg := sc_finite_function_l (ZF.modelsKP hZF) hω hX (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).pair (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).union hωX (fun _ h => h) hn (fn0_of_function_l (ZF.modelsKP hZF) fg)
  obtain ⟨C, hC, bound⟩ := (theory.algebra_l _ (ZF.modelsKP hZF) hX hm).envelope_l hg
  let η : Env M 2 := ⟨Fin.cases D (fun _ => C), fun _ => D⟩
  let ψ : UnarySchema 2 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)) }
  have ps p : ψ.denote η p ↔ ∃ a, M.mem a D ∧ ∃ b, M.mem b C ∧ KPair_d M p a b := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨q, hq, qs⟩ := sc_separate_source_l I hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) η (Fin.cases hD (fun _ => hC)) hg
  have eq : q = f := hZF.1.eq_of_same_members q f fun p => by
    constructor
    · intro hp
      obtain ⟨hp, hs⟩ := (qs p).mp hp
      obtain ⟨a, ha, b, _, pair⟩ := (ps p).mp hs
      have hb : Rd_entry_d a b f := ((read a b).mp ((spec a b).mp ⟨p, pair, hp⟩).2).elim And.right (fun h => (h.1 ha).elim)
      obtain ⟨r, hr, hrf⟩ := hb
      exact kpair_unique_l M hZF.1 hr pair ▸ hrf
    · intro hp
      obtain ⟨a, ha, b, _, pair⟩ := hf.1 p hp
      have hb := (spec a b).mpr ⟨sub a ha, (read a b).mpr (Or.inl ⟨ha, p, pair, hp⟩)⟩
      have hbc := (bound a b hb).2
      obtain ⟨r, hr, hrg⟩ := hb
      exact (qs p).mpr ⟨kpair_unique_l M hZF.1 hr pair ▸ hrg, (ps p).mpr ⟨a, ha, b, hbc, pair⟩⟩
  exact eq ▸ hq

end YesMetaZFC.SetTheory.Internal
