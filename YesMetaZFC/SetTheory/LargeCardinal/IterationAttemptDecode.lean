import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptRow
import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection

/-! # 联合尝试枝解码出相容的完整初等嵌入列

每条腿都有唯一图，所以替代收集整列。不同腿的交换律在同一个较长节点
中检查；目标不必被嵌入像覆盖，正好适用于嵌回固定秩段的情形。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem ja_common_l {ω T Q G E Y W z π A R g B i j a b u v : M.Domain}
    (h : It_order_d ω T) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B)
    (hu : Ja_observe_d g i a u) (hv : Ja_observe_d g j b v) :
    ∃ k P p q, Ja_node_d I ω T Q G E Y W z π k P ∧
      Rd_entry_d i p P ∧ Rd_entry_d j q P ∧ Rd_entry_d a u p ∧ Rd_entry_d b v q := by
  obtain ⟨n, s, k, P, p, hs, hp, hip, hau⟩ := hu
  obtain ⟨m, t, l, Q', q, ht, hq, hjq, hbv⟩ := hv
  have np := space.node_l hZF (fg.bound_l hs).2 hp
  have nq := space.node_l hZF (fg.bound_l ht).2 hq
  have move {i k l P Q' p a u} (np : Ja_node_d I ω T Q G E Y W z π k P)
      (nq : Ja_node_d I ω T Q G E Y W z π l Q') (hkl : Rd_entry_d k l T)
      (sub : ∀ i p q, Rd_entry_d i p P → Rd_entry_d i q Q' → M.MemberSubset p q)
      (hip : Rd_entry_d i p P) (hau : Rd_entry_d a u p) : ∃ q, Rd_entry_d i q Q' ∧ Rd_entry_d a u q := by
    obtain ⟨q, hiq⟩ := (nq.domain i).mpr (h.trans i k l ((np.domain i).mp ⟨p, hip⟩) hkl)
    obtain ⟨r, hr, hrp⟩ := hau
    exact ⟨q, hiq, r, hr, sub i p q hip hiq r hrp⟩
  rcases h.ordinal.wellOrder.linear.compare n (fg.bound_l hs).1 m (fg.bound_l ht).1 with eq | hnm | hmn
  · have eq := hZF.1.eq_of_same_members n m eq
    subst m
    have st := (fn0_function_l (ZF.modelsKP hZF) fg).1.2 n s t hs ht
    have pq := (kpair_injective_l M (st ▸ hp) hq).2
    exact ⟨l, Q', p, q, nq, pq ▸ hip, hjq, hau, hbv⟩
  · have ext := (path.chain n m s t hnm hs ht).read_l hp hq
    obtain ⟨p', hip', hau'⟩ := move np nq ext.2.1 ext.2.2 hip hau
    exact ⟨l, Q', p', q, nq, hip', hjq, hau', hbv⟩
  · have ext := (path.chain m n t s hmn ht hs).read_l hq hp
    obtain ⟨q', hjq', hbv'⟩ := move nq np ext.2.1 ext.2.2 hjq hbv
    exact ⟨k, P, p, q', np, hip, hjq', hau, hbv'⟩

theorem ja_decode_l {ω T Q G E Y W z π A R g B d : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (my : Smdl_d I d Y W) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B) :
    ∃ P, It_embedding_d hZF ω B Q G d Y W P ∧ ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ Ja_leg_d E g i f := by
  let φ : BinarySchema 2 := { body := ja_leg_m (.bound 2) (.bound 3) (.bound 1) .newest }
  let ρ : Env M 2 := ⟨Fin.cases E (fun _ => g), fun _ => g⟩
  have sat i f : φ.denote ρ i f ↔ Ja_leg_d E g i f := ja_leg_sat_l (ZF.modelsKP hZF) ..
  have total i (hi : M.mem i B) : ∃ f, φ.denote ρ i f := by
    obtain ⟨c, X, V, hc, mx⟩ := h.model_l hZF (path.branch.subset i hi)
    obtain ⟨e, he⟩ := (en.domain i).mp (path.branch.subset i hi)
    obtain ⟨f, _, hf⟩ := ja_row_l hZF hω en my space fg path hi hc mx he
    exact ⟨f, (sat i f).mpr hf⟩
  have unique i f j (hf : φ.denote ρ i f) (hj : φ.denote ρ i j) : f = j :=
    ((sat i f).mp hf).unique_l (ZF.modelsKP hZF) ((sat i j).mp hj)
  obtain ⟨D, hd⟩ := ZF.exists_functionalImage hZF φ ρ B total unique
  obtain ⟨P, pf, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total (fun i _ => unique i)
    (fun i f hi hf => (hd f).mpr ⟨i, hi, hf⟩)
  have read i f : Rd_entry_d i f P ↔ M.mem i B ∧ Ja_leg_d E g i f :=
    (ps i f).trans (and_congr_right fun _ => sat i f)
  have typed i f c X V (hf : Rd_entry_d i f P) (hc : Rd_entry_d i c Q) (mx : Smdl_d I c X V) :
      Smap_d I ω c d X Y f := by
    obtain ⟨e, he⟩ := (en.domain i).mp (path.branch.subset i ((read i f).mp hf).1)
    obtain ⟨j, hj, js⟩ := ja_row_l hZF hω en my space fg path ((read i f).mp hf).1 hc mx he
    exact js.unique_l (ZF.modelsKP hZF) ((read i f).mp hf).2 ▸ hj
  refine ⟨P, ⟨my, pf.1, pf.2.1, typed, ?_⟩, read⟩
  intro i j f u v hf hu hv x y a hxy hya
  obtain ⟨ci, X, S, hci, mx⟩ := h.model_l hZF (path.branch.subset i ((read i u).mp hu).1)
  obtain ⟨cj, Z, V, hcj, mz⟩ := h.model_l hZF (path.branch.subset j ((read j v).mp hv).1)
  have elem := typed i u ci X S hu hci mx
  have hx := (h.elementary i j f ci X S cj Z V hf hci hcj mx mz).1.1.input_mem_of_pairMember hxy
  obtain ⟨b, _, hxb⟩ := elem.1.1.2.2 x hx
  obtain ⟨e, n, he, hnx, hnb⟩ := (((read i u).mp hu).2.2 x b).mp hxb
  obtain ⟨e', m, he', hmy, hma⟩ := (((read j v).mp hv).2.2 y a).mp hya
  obtain ⟨k, H, p, q, node, hp, hq, hnp, hmq⟩ := ja_common_l hZF h.order space fg path hnb hma
  exact node.commute i j p q e e' f n m x y b a hp hq he he' hf hnx hmy hxy hnp hmq ▸ hxb

/-- 根行的原图由有限限制恢复；这里只需要原图是全定义函数。 -/
theorem ja_root_l {ω T Q G E Y W z π A R g B P c X V : M.Domain}
    (en : Ja_enum_d I ω ω Q E) (space : Ja_space_d I ω T Q G E Y W z π A R)
    (fg : Fn0_d ω A g) (path : Ja_path_d ω T g B) (hz : M.mem z B)
    (hc : Rd_entry_d z c Q) (mx : Smdl_d I c X V) (fπ : Fn0_d X Y π)
    (maps : ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ Ja_leg_d E g i f)
    (fn : ∀ f, Rd_entry_d z f P → Fn0_d X Y f) (domain : ∃ f, Rd_entry_d z f P) : Rd_entry_d z π P := by
  obtain ⟨f, hf⟩ := domain
  obtain ⟨e, he⟩ := (en.domain z).mp (path.branch.subset z hz)
  have eq : π = f := fπ.ext_l hZF.1 (fn f hf) (fun x hx => by
    obtain ⟨y, hy, hxy⟩ := fπ.2.1 x hx
    obtain ⟨a, ha, hax⟩ := (en.rows z e c X V he hc mx.1).2 x hx
    obtain ⟨n, s, k, H, hs, hp, hzk, hak⟩ := path.wide z a hz ha
    have node := space.node_l hZF (fg.bound_l hs).2 hp
    obtain ⟨p, hzp⟩ := (node.domain z).mpr hzk
    have hay := node.root p c X V e hzp hc mx.1 he a hak x hx y hy hax hxy
    exact ⟨y, hxy, (((maps z f).mp hf).2.2 x y).mpr ⟨e, a, he, hax, n, s, k, H, p, hs, hp, hzp, hay⟩⟩)
  exact eq.symm ▸ hf

end YesMetaZFC.SetTheory.LargeCardinal
