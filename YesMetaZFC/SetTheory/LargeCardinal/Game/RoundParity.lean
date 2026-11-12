import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.Ord.Recursion
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.FiniteArithmeticSource

/-! # 原模型轮号与外部档案索引

数字图把当前原轮号读回背景自然数。较早原轮号自动选择外部序列中的
实际行；原关系中的每个后继也来自同一背景后继，追加档案时无需改写旧行。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Tg_round_index_d {X R : M.Domain} (Ω z : M.Domain) (nx : ∃ x, M.mem x X)
    (w n : (smdl_structure_l I (R := R) nx).Domain) (m : M.Domain) : Prop where
  numbers : Rr_layer_d I Ω X R w.val z
  omega : M.IsOmega Ω
  finite : M.mem m Ω
  point : M.PairMember I m n.val z
  select : ∀ H, M.IsSequenceOfLength I H m → ∀ k, M.PairMember I k n.val R →
    ∃ l r, M.mem l m ∧ M.PairMember I l k z ∧ M.PairMember I l r H
  next : ∀ n' : (smdl_structure_l I (R := R) nx).Domain,
      (smdl_structure_l I (R := R) nx).SuccessorOf n' n →
      ∃ m', M.mem m' Ω ∧ M.SuccessorOf m' m ∧ M.PairMember I m' n'.val z ∧
        ∀ H, M.IsSequenceOfLength I H m → ∀ r,
          ∃ H', M.IsSequenceOfLength I H' m' ∧
            ∀ l s, M.PairMember I l s H' ↔ M.PairMember I l s H ∨ l = m ∧ s = r

/-- 完整数字图同时完成旧行选择和下一轮索引的构造。 -/
theorem tg_round_index_l (hKP : M.Models KP) {Ω X R z : M.Domain}
    (hΩ : M.IsOmega Ω) (nx : ∃ x, M.mem x X)
    (ext : Extensional (smdl_structure_l I (R := R) nx))
    (w n : (smdl_structure_l I (R := R) nx).Domain)
    (numbers : Rr_layer_d I Ω X R w.val z)
    (hn : (smdl_structure_l I (R := R) nx).mem n w) :
    ∃ m, Tg_round_index_d I Ω z nx w n m := by
  obtain ⟨m,hm,mn⟩ := (numbers.image n.val).mp hn
  refine ⟨m,numbers,hΩ,hm,mn,?_,?_⟩
  · intro H seq k hk
    obtain ⟨l,hl,lk⟩ := (numbers.predecessors m n.val mn k).mp hk
    obtain ⟨r,lr⟩ := (seq.2.2 l).mp hl
    exact ⟨l,r,hl,lk,lr⟩
  · intro n' step
    obtain ⟨m',next,hm'⟩ := hΩ.1.2 m hm
    obtain ⟨p,hp,mp⟩ := numbers.injection.1.2.2 m' hm'
    have succ := numbers.successor_l I hKP.1 ext n ⟨p,hp⟩ mn mp next
    have eq := congrArg Subtype.val (succ.eq ext step)
    refine ⟨m',hm',next,eq ▸ mp,?_⟩
    intro H seq r
    exact Structure.IsSequenceOfLength.exists_append (value := r) hKP I
      seq (KP.successor_isOrdinal hKP seq.1 next) next

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一外部轮号与反射层中的回合条件

完整数字图先比较背景与所属模型的奇偶，有限读出层的加法绝对性再将
实际控制公式读回所属模型。这里只连接已有真实索引，不重新选择轮号。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_round_index_d.even_l {Ω X R z m : M.Domain} {nx : ∃ x, M.mem x X}
    {w n C : (smdl_structure_l I (R := R) nx).Domain}
    (h : Tg_round_index_d I Ω z nx w n m)
    (hN : (smdl_structure_l I (R := R) nx).Models ZF)
    (fs : Fs_read_d (M := smdl_structure_l I (R := R) nx) w C)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) nx).Domain //
      (smdl_structure_l I (R := R) nx).mem x C})
    {d} (ρ : Env (rt_model_l C nc) d) (a b : Term d)
    (hw : (a.eval ρ).val = w) (hn : (b.eval ρ).val = n) :
    Formula.satisfies ρ (gm_even_m (𝒞 := kpair_convention_l) a b) ↔ Gm_even_d I Ω m := by
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ext := rt_model_ext_l hN.1 fs.transitive nc
  have omegaN := h.numbers.omega_l I (ZF.modelsKP hZF) h.omega hN.1
  have native := h.numbers.even_l hZF h.omega hN h.finite n h.point
  have reflected := fs_even_l hN omegaN fs nc (a.eval ρ) (b.eval ρ) hw
  rw [hn] at reflected
  exact (gm_even_sat_l J ext ρ a b).trans (reflected.trans native.symm)

end YesMetaZFC.SetTheory.LargeCardinal
