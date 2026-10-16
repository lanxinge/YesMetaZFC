import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentative

/-! # 原始商中任意有限组对象的共同支撑代表

逐个合并实际支撑，再把全部旧代表拉回同一分量。代表只从源中取得，
有限组装不用全局选择；随后函数求值可以直接接受商对象而不索要代表参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_finite_representatives_l {ω κ K L X R F J O Z A p T S q C W : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    {k : Nat} (v : Fin k → M.Domain) (members : ∀ i, M.mem (v i) C) :
    ∃ n a D, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧
      ∃ f : Fin k → M.Domain, ∀ i, M.mem (f i) X ∧ Fn0_d D X (f i) ∧ Ep_repr_d q a (f i) (v i) := by
  have collect : ∀ k (P : Fin k → M.Domain → Prop), (∀ i, ∃ x, P i x) → ∃ f : Fin k → M.Domain, ∀ i, P i (f i) := by
    intro k
    induction k with
    | zero => exact fun _ _ => ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ k ih =>
      intro P total
      obtain ⟨x, hx⟩ := total 0
      obtain ⟨f, hf⟩ := ih (fun i => P i.succ) (fun i => total i.succ)
      exact ⟨Fin.cases x f, Fin.cases hx hf⟩
  induction k with
  | zero =>
    obtain ⟨z, hz, hzw⟩ := source.omega.1.1
    have empty : Fn0_d z L z := ⟨fun p hp => (hz p hp).elim, fun i hi => (hz i hi).elim, fun i hi => (hz i hi).elim⟩
    obtain ⟨D, _, space⟩ := source.space_l hZF hzw
    exact ⟨z, z, D, hzw, (system.indices z).mpr ⟨z, hzw, empty, fun i j x hi _ =>
      (hz i (empty.bound_l hi).1).elim⟩, empty, space, Fin.elim0, fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨n, a, D, f, hn, haJ, ha, space, hf, ff, value⟩ := ep_repr_surjective_l hZF family system limit (members 0)
    obtain ⟨m, b, E, hm, hbJ, hb, space', g, gs⟩ := ih (fun i => v i.succ) (fun i => members i.succ)
    obtain ⟨c, hcJ, hac, hbc⟩ := system.order.directed a b haJ hbJ
    obtain ⟨l, hl, hc, _⟩ := (system.indices c).mp hcJ
    obtain ⟨Q, _, sq⟩ := source.space_l hZF hl
    have move {n a D f H} (hn : M.mem n ω) (ha : Fn0_d n L a) (space : Ep_space_d κ n D)
        (hf : M.mem f X) (ff : Fn0_d D X f) (value : Ep_repr_d q a f H) (edge : Rd_entry_d a c O) :
        ∃ g, M.mem g X ∧ Fn0_d Q X g ∧ Ep_repr_d q c g H := by
      obtain ⟨_, _, r, n', l', _, _, fr, hc', comp⟩ := (system.order_spec a c).mp edge
      have en := comp.1.domain_eq_l hZF.1 ha
      have el := hc'.domain_eq_l hZF.1 hc
      subst n' l'
      obtain ⟨g, hg, fg, _, gv⟩ := ep_repr_reindex_l hZF source family system limit hn hl fr hcJ hc comp space sq hf ff value
      exact ⟨g, hg, fg, gv⟩
    obtain ⟨f', hf'⟩ := move hn ha space hf ff value hac
    obtain ⟨g', hg'⟩ := collect k (fun i g => M.mem g X ∧ Fn0_d Q X g ∧ Ep_repr_d q c g (v i.succ))
      (fun i => move hm hb space' (gs i).1 (gs i).2.1 (gs i).2.2 hbc)
    exact ⟨l, c, Q, hl, hcJ, hc, sq, Fin.cases f' g', Fin.cases hf' hg'⟩

end YesMetaZFC.SetTheory.LargeCardinal
