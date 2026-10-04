"""Regression checks for compiler dependency and configuration boundaries."""

import contextlib
import copy
import io
import unittest
from unittest import mock

import gen


class ComponentBoundaries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = gen.load_manifest()
        cls.imports = gen.component_imports(cls.manifest)

    def boundary_failures(self, manifest, imports=None):
        report = gen.Report(strict=True)
        with contextlib.redirect_stdout(io.StringIO()) as output:
            gen.verify_boundaries(manifest, report, imports or self.imports)
        return report.failures, output.getvalue()

    def with_dependency(self, package, dependency):
        manifest = copy.deepcopy(self.manifest)
        next(c for c in manifest['components'] if c['name'] == package)['depends'].append(dependency)
        return manifest

    def test_current_boundaries(self):
        failures, output = self.boundary_failures(self.manifest)
        self.assertEqual(failures, 0, output)

    def test_executables_and_tests_have_total_home_module_dags(self):
        report = gen.Report(strict=True)
        with contextlib.redirect_stdout(io.StringIO()) as output:
            gen.verify_e(self.manifest, report, self.imports)
        self.assertEqual(report.failures, 0, output.getvalue())
        self.assertIn('11 total home-module DAGs', output.getvalue())

    def test_unordered_executable_helpers_are_rejected(self):
        original = gen.imports_of

        def omit_ordering_import(path):
            imports = original(path)
            if path.name == 'TclUtils.hs':
                imports = [mod for mod in imports if mod != 'BluesimLoader']
            return imports

        report = gen.Report(strict=True)
        with mock.patch.object(gen, 'imports_of', side_effect=omit_ordering_import):
            with contextlib.redirect_stdout(io.StringIO()) as output:
                gen.verify_e(self.manifest, report, self.imports)
        self.assertGreater(report.failures, 0)
        self.assertIn('executable bluetcl: unordered home modules:', output.getvalue())

    def test_global_configuration_stays_with_driver(self):
        imports = copy.deepcopy(self.imports)
        imports['bsc-typecheck']['TypeCheck'].append('Flags')
        failures, output = self.boundary_failures(self.manifest, imports)
        self.assertGreater(failures, 0)
        self.assertIn('TypeCheck (bsc-typecheck) imports driver configuration Flags', output)

    def test_parser_and_typechecker_are_independent(self):
        for package, forbidden in [('bsc-parse', 'bsc-typecheck'), ('bsc-typecheck', 'bsc-parse')]:
            with self.subTest(package=package):
                self.assertNotIn(forbidden, gen.component_closure(self.manifest, [package]))
                failures, output = self.boundary_failures(self.with_dependency(package, forbidden))
                self.assertGreater(failures, 0, output)

    def test_package_artifact_closure_excludes_module_compilation(self):
        closure = set(gen.component_closure(self.manifest, ['bsc-parse', 'bsc-typecheck', 'bsc-package']))
        self.assertFalse(closure & {'bsc-elab', 'bsc-scheduled', 'bsc-schedule', 'bsc-verilog', 'bsc-bluesim'})
        failures, output = self.boundary_failures(self.with_dependency('bsc-package', 'bsc-schedule'))
        self.assertGreater(failures, 0)
        self.assertIn('package artifacts closure includes unrelated implementation: bsc-schedule', output)

    def test_frontend_cannot_acquire_a_backend_transitively(self):
        failures, output = self.boundary_failures(self.with_dependency('bsc-typecheck', 'bsc-verilog'))
        self.assertGreater(failures, 0)
        self.assertIn('frontend component bsc-elab depends on backend components', output)

    def test_solver_adapters_remain_independent(self):
        failures, output = self.boundary_failures(self.with_dependency('bsc-yices', 'bsc-common'))
        self.assertGreater(failures, 0)
        self.assertIn('solver adapter bsc-yices depends on compiler components', output)

    def test_common_does_not_inherit_solver_link_flags(self):
        manifest = copy.deepcopy(self.manifest)
        next(c for c in manifest['components'] if c['name'] == 'bsc-common')['extras'] = {'extra-libraries-other': ['stdc++']}
        failures, output = self.boundary_failures(manifest)
        self.assertGreater(failures, 0)
        self.assertIn('shared substrate bsc-common declares native link/build settings', output)

    def test_legacy_reader_writer_are_explicit_app_dependencies(self):
        components = gen.facade_components(self.manifest)
        self.assertNotIn('bsc-legacy-ba', gen.component_closure(self.manifest, [c['name'] for c in components]))
        failures, output = self.boundary_failures(self.with_dependency('bsc-scheduled', 'bsc-legacy-ba'))
        self.assertGreater(failures, 0)
        self.assertIn('compiler phase libraries closure includes unrelated implementation: bsc-legacy-ba', output)

    def test_codecs_do_not_depend_on_phase_algorithms(self):
        failures, output = self.boundary_failures(self.with_dependency('bsc-legacy-ba', 'bsc-schedule'))
        self.assertGreater(failures, 0)
        self.assertIn('artifact codecs closure includes unrelated implementation: bsc-schedule', output)

    def test_schedule_data_does_not_depend_on_scheduler_implementation(self):
        failures, output = self.boundary_failures(self.with_dependency('bsc-scheduled', 'bsc-schedule'))
        self.assertGreater(failures, 0)
        self.assertIn('scheduled representation closure includes unrelated implementation: bsc-schedule', output)

    def test_backends_do_not_depend_on_each_other_or_the_scheduler(self):
        for backend, peer in [('bsc-verilog', 'bsc-bluesim'), ('bsc-bluesim', 'bsc-verilog')]:
            for dependency in (peer, 'bsc-schedule'):
                with self.subTest(backend=backend, dependency=dependency):
                    self.assertNotIn(dependency, gen.component_closure(self.manifest, [backend]))
                    failures, output = self.boundary_failures(self.with_dependency(backend, dependency))
                    self.assertGreater(failures, 0, output)

    def test_git_provenance_does_not_enter_phase_implementation_closures(self):
        self.assertEqual(self.manifest['_owner']['CompilerVersion'], 'bsc-common')
        for module in ('Version', 'BuildVersion'):
            with self.subTest(module=module):
                self.assertEqual(self.manifest['_owner'][module], 'bsc-driver')
                imports = copy.deepcopy(self.imports)
                imports['bsc-common']['ErrorUtil'].append(module)
                failures, output = self.boundary_failures(self.manifest, imports)
                self.assertGreater(failures, 0)
                self.assertIn('ErrorUtil (bsc-common) imports driver Git provenance ' + module, output)

    def test_build_policy_flags_and_native_sources_have_single_owners(self):
        owners = {flag['name']: c['name'] for c in self.manifest['components']
                  for flag in c.get('flags', [])}
        self.assertEqual(owners, {'no-git': 'bsc-driver',
                                  'no-update-build-version': 'bsc-driver',
                                  'stp-stub': 'bsc-stp', 'yices-stub': 'bsc-yices'})
        for component in self.manifest['components']:
            rendered = gen.render_component_cabal(self.manifest, component)
            self.assertNotIn('.git/', rendered)
            for flag in component.get('flags', []):
                self.assertIn('flag ' + flag['name'] + '\n', rendered)
            sources = component.get('extra-source-files', [])
            if sources:
                self.assertIn(component['name'], ('bsc-stp', 'bsc-yices'))
                solver = component['name'].removeprefix('bsc-')
                self.assertIn('src/vendor/' + solver + '/Makefile', sources)
                self.assertTrue(all(path.startswith(('platform.', 'src/vendor/' + solver + '/'))
                                    for path in sources))

    def test_scheduler_does_not_pull_in_physical_port_analysis(self):
        imports = copy.deepcopy(self.imports)
        imports['bsc-schedule']['AAddScheduleDefs'].append('BackendNamingConventions')
        failures, output = self.boundary_failures(self.manifest, imports)
        self.assertGreater(failures, 0)
        self.assertIn('scheduler physical naming exclusion imports forbidden APIs: BackendNamingConventions', output)


if __name__ == '__main__':
    unittest.main()
