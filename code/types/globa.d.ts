declare const ace: any

interface Context {
    editor: any;
    language: string;
    readonly: boolean;
}
interface Window {
    gobraBookEditorContext: Map<string, Context>;
    playground_line_numbers: boolean;
}